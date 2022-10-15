#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2019-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#
import copy, itertools, simplejson as json, pprint as pp, random, time, traceback
import psycopg2, psycopg2.extras

import mgsmt.experiments.server
from mgsmt.experiments.server import enqueue_job, wait_on_running_job
#------------------------------------------------------------------------------#

class ExperimentRunner:

    def __init__(self, inference_experiment):
        self.inf_exp = inference_experiment


    def process_detection_parameter_map(self, detection_param_map):
        raise NotImplemented


    def run(self, checkpoint_filepath=None, run_from_checkpoint=False, verbose=False):
        if run_from_checkpoint:
            assert checkpoint_filepath

        try:
            if not(run_from_checkpoint):
                p_inference = self.inf_exp.run()
                detection_param_map = next(p_inference)

            if checkpoint_filepath:
                if not(run_from_checkpoint):
                    with open(checkpoint_filepath, 'w') as f_out:
                        json.dump(detection_param_map, f_out)
                with open(checkpoint_filepath, 'r') as f_in:
                    detection_param_map = json.load(f_in)

            for e_idx in itertools.count(0):
                blocking_constraints = self.process_detection_parameter_map(detection_param_map)
                if blocking_constraints:
                    detection_param_map = p_inference.send(blocking_constraints)
                else:
                    self.inf_exp.log(msg="No overgenerations were detected.")
                    break
        finally:
            p_inference.close()
            print("End of Inference Procedure.")

#------------------------------------------------------------------------------#

class SequentialExperimentRunner(ExperimentRunner):

    def process_detection_params(self, df_id, detection_params):
        other_args = {"display.jupyter-widgets": True}
        od_experiment = mgsmt.experiments.overgenerationdetectionexperiment.OvergenerationDetectionExperiment(params=detection_params,
                                                            other_args=other_args,
                                                            verbose=True)
        blocking_constraints = od_experiment.run()
        if blocking_constraints:
            return blocking_constraints
        else:
            self.inf_exp.log(msg=f"Did not detect overgenerations for derivation {df_id}.")
            return []


    def process_detection_parameter_map(self,
                                        detection_param_map,
                                        only_first=False,
                                        verbose=False):
        results = {}
        for df_id, detection_param in detection_param_map.items():
            if verbose:
                self.inf_exp.log(msg=f"Processing DF_id: {df_id}.")
            results[df_id] = self.process_detection_params(df_id, detection_param)
            if only_first:
                if len(results[df_id]) > 0:
                    break

        return results

#------------------------------------------------------------------------------#

class ParallelExperimentRunner(ExperimentRunner):

    def __init__(self, inference_experiment, db_params=None):
        if not db_params:
            db_params = {"user": "indurks",
                         "host": "18.21.165.206",
                         "port": "5432",
                         "database": "mgsmt",
                         "password": "S1123581321i"}
        self.db_params = db_params
        super(ParallelExperimentRunner, self).__init__(inference_experiment)


    def submit_jobs(self, detection_param_map, retry=False, retry_interval_seconds=5):
        input_json_map = json.dumps(detection_param_map)
        self.inf_exp.log(msg="Submitting the jobs.")
        print("Submitting")
        print(detection_param_map)
        while True:
            try:
                job_ids = {}
                with psycopg2.connect(**self.db_params) as conn:
                    for df_id, dp in detection_param_map.items():
                        input_json = json.dumps(dp)
                        job_ids[df_id] = enqueue_job(conn, input_json, '1 hour')
                        self.inf_exp.log(msg=f"job_ids[{df_id}] = {job_ids[df_id]}")
                return job_ids
            except (Exception, psycopg2.Error) as error:
                self.inf_exp.log(msg="Error while connecting to PostgreSQL: " + str(error))
                if retry:
                    self.inf_exp.log(msg=f"Resubmitting the jobs in {retry_interval_seconds}s.")
                    time.sleep(retry_interval_seconds)
                else:
                    raise


    def collect_job_results(self, job_ids, retry=True, retry_interval_seconds=5):
        while True:
            self.inf_exp.log(msg="Collecting results from the jobs.")
            try:
                results = {}
                with psycopg2.connect(**self.db_params) as conn:
                    for df_id, job_id in job_ids.items():
                        results[df_id] = wait_on_running_job(conn, job_id)
                        self.inf_exp.log(msg=f"results[{df_id}] = {results[df_id]}")
                return results
            except (Exception, psycopg2.Error) as error:
                self.inf_exp.log(msg="Error while connecting to PostgreSQL" + str(error))
                if retry:
                    self.inf_exp.log(msg=f"Retrying collection of job results in {retry_interval_seconds}s.")
                    time.sleep(retry_interval_seconds)
                else:
                    raise


    def process_detection_parameter_map(self, detection_param_map):
        detection_param_map = copy.deepcopy(detection_param_map)

        # Break the dpm into per-derivation dpms.
        for k, v in detection_param_map.items():
            v['df_id'] = k

        try:
            job_ids = self.submit_jobs(detection_param_map)
            results = self.collect_job_results(job_ids)
            return results
        except:
            traceback.print_exc()
            raise
