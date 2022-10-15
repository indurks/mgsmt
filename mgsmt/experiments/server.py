#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import psycopg2
import psycopg2.extras
import simplejson as json
import argparse, getpass, pprint as pp, time

"""
CREATE TYPE job_status AS ENUM(
'queued', 'running', 'completed', 'timeout', 'error', 'canceled');

CREATE TABLE jobs(
id SERIAL PRIMARY KEY,
status job_status NOT NULL,
enqueue_ts TIMESTAMP NOT NULL,
timeout INTERVAL NOT NULL,
input JSONB NOT NULL,
output JSONB default NULL,
worker_info JSONB default NULL,
start_ts TIMESTAMP default NULL,
end_ts TIMESTAMP default NULL);
"""

SQL_INSERT_1 = """
INSERT INTO jobs
VALUES (DEFAULT, 'queued', now(), %s :: interval, %s, NULL, NULL, NULL, NULL)
RETURNING id;
"""

SQL_QUERY_1 = """
SELECT output FROM jobs WHERE id = %s and status = 'completed' LIMIT 1;  
"""

def load_input(input_json_fp):
    # Load in the experiment config file.
    print("opening " + input_json_fp)
    with open(input_json_fp, 'r') as f_input:
        input_json = json.dumps(json.load(f_input))
        return input_json


def enqueue_job(conn, input_json, timeout):
    with conn.cursor() as cursor:
        cursor.execute(SQL_INSERT_1, (timeout, input_json))
        job_id = cursor.fetchone()
        return job_id

def wait_on_running_job(conn, job_id):
    # Wait until either the experiment no longer running or the timeout
    # has been exceeded.
    while True:
        with conn.cursor() as cursor:
            cursor.execute(SQL_QUERY_1, (job_id,))
            row = cursor.fetchone()
            conn.commit()
            if row:
                print(f"Read the completed result of job: {job_id}.")
                print(f"Output: {row[0]}")
                return row[0]


def main(db_params, timeout=None, input_json_fp=None, verbose=False):
    try:
        with psycopg2.connect(**db_params) as conn:
            input_json = load_input(input_json_fp)
            job_id = enqueue_job(conn, input_json, '1 hour')
            wait_on_running_job(conn, job_id)
    except (Exception, psycopg2.Error) as error:
        print ("Error while connecting to PostgreSQL", error)
    finally:
        print("PostgreSQL connection is closed")


if __name__ == '__main__':
    db_params = {"user": "indurks",
                 "host": "18.21.165.206",
                 "port": "5432",
                 "database": "mgsmt"}
    #db_params["password"] = getpass.getpass("db password: ")
    db_params["password"] = 'skrudni'

    parser = argparse.ArgumentParser()
    parser.add_argument("-f", "--file",
                        dest="filename",
                        help="read job input from FILE",
                        metavar="FILE",
                        required=True)
    parser.add_argument("-v", "--verbose",
                        action="store_true",
                        dest="verbose",
                        default=False)
    args = parser.parse_args()

    num_instances = 1000
    for i in range(num_instances):
        main(db_params=db_params,
             input_json_fp=args.filename,
             verbose=args.verbose)
