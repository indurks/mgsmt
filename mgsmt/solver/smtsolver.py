#!/usr/bin/env python3

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

import copy, itertools, json, multiprocessing, os, pathlib, pprint as pp
import signal, sys, time, uuid, traceback
from collections import namedtuple, OrderedDict
from contextlib import contextmanager
from func_timeout import func_timeout, FunctionTimedOut
from z3 import *

import mgsmt.models.lexiconmodel
import mgsmt.models.derivationmodel

def fork_and_check_worker(solver, constraint, conn):
    if constraint == None:
        result = solver.check()
    else:
        result = solver.check(constraint)
    
    conn.send(result)
    conn.close()


def fork_and_check_with_timeout(solver, timeout, constraint=None):
    assert type(timeout) ==  int
    assert 0 < timeout
    parent_conn, child_conn = multiprocessing.Pipe()
    args = (solver, constraint, child_conn)
    p = multiprocessing.Process(target=fork_and_check_worker, args=args)
    p.start()
    child_conn.close()

    normalized_timeout = max(1, int(timeout/1000.0))
    # Timeout after a designated interval.
    def sighandler(signo, stack):
        print(f"Timed out: {normalized_timeout}s.")
        p.terminate()

    signal.signal(signal.SIGALRM, sighandler)
    signal.alarm(normalized_timeout)

    try:
        result = parent_conn.recv()
    except EOFError:
        result = z3.unknown
    finally:
        signal.alarm(0) # Kill the alarm.

    p.join()
    return result


class SMTSolverException(Exception):

    def __init__(self, z3_output):
        self.z3_output = z3_output

    def __str__(self):
        return f"[SMTSolverException -- result: {self.z3_output}]"


class SMTSolver:

    OPTIMIZATION_TIMEOUT_MILLISECONDS = 1000*60*60*12

    def __init__(self,
                 parameters,
                 validate_negations_are_unsatisfiable=False,
                 log_fn=None):
        assert isinstance(parameters, dict), parameters
        self.params = parameters
        self.model = None
        self.check_counter = 0
        self.z3_add_elapsed_time = 0
        self.total_check_elapsed_time = 0
        self.total_construct_elapsed_time = 0
        self.tag_stack = []
        self.log_fn = log_fn
        self.timeout_value = 'infty'
        self.solver = Solver()
        self.validate_negations_are_unsatisfiable = validate_negations_are_unsatisfiable


    def set_timeout(self, timeout, verbose=True):
        assert timeout == 'infty' or (type(timeout) == int and 0 < timeout), (timeout, type(timeout))
        self.timeout_value = timeout
        if verbose:
            self.log_msg(msg=f"[SMT-Solver] Set Solver Timeout: {self.timeout_value}ms.")
            sys.stdout.flush()


    #------------------------------------------------------------------------------#
    # Adding Constraints
    #------------------------------------------------------------------------------#
    def validate_unsat_of_negation(self, term):
        # check for unsat if we assert the negation of the term.
        self.solver.push()
        self.solver.add(Not(term))
        result = str(self.solver.check())
        self.solver.pop()
        return result


    def validate_conj(self, conjuncts):
        if self.validate_negations_are_unsatisfiable:
            with self.group(tag='Validate unsatisfiability of negation'):
                assert 'unsat' == self.validate_unsat_of_negation(And(list(conjuncts)))


    def add(self, term, simplify=True, check_negation_is_unsat=False):
        t_start = time.time()
        if simplify:
            term = z3.simplify(term)
        if check_negation_is_unsat:
            if self.validate_unsat_of_negation(term) == 'unsat':
                self.log_msg("Checked for unsatisfiability of negation: UNSATISFIABLE")
        self.solver.add(term)
        self.z3_add_elapsed_time += float(time.time() - t_start)


    def add_singleton(self, term):
        return self.add_conj([term])


    def add_conj(self, conjuncts):
        with self.group(check_model=self.params['check_model']):
            self.add(And([x for x in conjuncts]), check_negation_is_unsat=False)


    #------------------------------------------------------------------------------#
    # Evaluation
    #------------------------------------------------------------------------------#
    def check(self, constraint=None, raise_exception_if_not_satisfiable=True):
        """Check whether the constraints added thus far are satisfiable.

        If the timeout is set at 'infty', this method will be run as
        long as required; otherwise this method will be forked and the
        child process will run until the timeout terminates the
        process.
        """
        t_start = time.time()

        if self.timeout_value == 'infty':
            if constraint != None:
                result = self.solver.check(constraint)
            else:
                result = self.solver.check()
        else:
            assert type(self.timeout_value) == int
            result = fork_and_check_with_timeout(self.solver,
                                                 timeout=self.timeout_value,
                                                 constraint=constraint)

        t_elapsed = time.time() - t_start
        self.total_check_elapsed_time += t_elapsed
        self.check_counter += 1

        if str(result) != 'sat' and raise_exception_if_not_satisfiable:
            self.log_msg(msg=f"[SMT-Solver] Solver Result: " + str(result))
            raise SMTSolverException(z3_output=result)
        else:
            return result, t_elapsed


    def evaluate_model(self):
        """Use the solver to check and interpret the model.
        """
        # Check that the (uninterpreted) model is satisfiable.
        with self.group(tag="Evaluating the model.", check_model=True):
            pass
        # Extract an interpretable model from the solver.
        self.model = self.solver.model()


    def evaluate_extract_all_parses(self,
                                    parser_lexicon_formula,
                                    parser_derivation_formula,
                                    num_parses_to_extract=3):
        assert parser_lexicon_formula is not None, parser_lexicon_formula
        assert parser_derivation_formula is not None, parser_derivation_formula
        self.log_msg("Extracting multiple parses.")
        self.evaluate_model()

        df = parser_derivation_formula
        lf = parser_lexicon_formula

        def extract_parse(model):
            lm = mgsmt.models.lexiconmodel.LexiconModel(lexicon_formula=lf, model=model)
            dm = mgsmt.models.derivationmodel.DerivationModel(derivation_formula=df, model=model)
            return (lm, dm)

        try:
            # Extract the initial parse.
            parses = [extract_parse(self.model)]
            self.log_msg(f"Extracted parse #{len(parses)} from the solver.")
            yield parses[-1]

            # Extract alternative parses.
            # (Note that it is worth studying the following SO post:
            # https://stackoverflow.com/questions/11867611/z3py-checking-all-solutions-for-equation)
            while len(parses) < num_parses_to_extract:
                # exclude the previously obtained parse.
                block = []
                bus = lf.derivations[df.formula_name]['bus']
                active_dnodes = [n for n in df.all_nodes()
                                 if self.model.eval(And([n != df.null_node,
                                                         df.head(n) != df.null_node]))]

                # Alternative parses may have different merge operations taking place.
                for x in active_dnodes:
                    for y in active_dnodes:
                        if self.model.eval(df.merged(x, y) != df.null_node) and (str(x) < str(y)):
                            alpha = And([df.pf_map(df.head(x)) == self.model.eval(df.pf_map(df.head(x))),
                                         df.pf_map(df.head(y)) == self.model.eval(df.pf_map(df.head(y))),
                                         df.cat_map(df.head(x)) == self.model.eval(df.cat_map(df.head(x))),
                                         df.cat_map(df.head(y)) == self.model.eval(df.cat_map(df.head(y))),
                                         df.merged(x, y) != df.null_node])
                            m_d = df.pf_map(df.head(df.merged(x, y)))
                            m_cat = df.cat_map(df.head(df.merged(x, y)))
                            beta = And([m_cat == self.model.eval(m_cat),
                                        m_d == self.model.eval(m_d)])
                            nt_x = lf.pfInterface.pf_node_type(df.pf_map(df.head(x)))
                            nt_y = lf.pfInterface.pf_node_type(df.pf_map(df.head(y)))
                            gamma = And([nt_x == lf.pfInterface.PFTypeSort.Overt,
                                         nt_y == lf.pfInterface.PFTypeSort.Overt])
                            block.append(And([Not(And([alpha, beta])), gamma]))
                
                # Alternative parses might or might not involve head-movement operations.
                for x in active_dnodes:
                    if self.model.eval(x == df.head(x)):
                        c = lf.head_movement(bus(x))
                        block.append(c != self.model.eval(c))
                
                self.log_msg(f"Derived {len(block)} *blocking constraints* that work to rule out the prior parse.")
                self.solver.add(Or(block))
                self.log_msg("Added blocking expression to the model.")
                st_exp_result = self.solver.check()
                self.log_msg(f"Checked model, result is: {st_exp_result}.")
                if str(st_exp_result) != 'sat':
                    break
                self.model = self.solver.model()
                parses.append(extract_parse(self.model))
                self.log_msg(f"Extracted parse #{len(parses)} from the solver.")
                yield parses[-1]
                """
                The following can help with debugging.
                # Now identify which of the constraints from the prior block were satisfied.
                self.log_msg("The following constraints from the prior block were satisfied:")
                for b in block:
                    if self.model.eval(b):
                        print(str(b))
                """
        except:
            traceback.print_exc()
            raise
        finally:
            self.log_msg(f"Extracted a total of {len(parses)} parses from the solver.")
            return None
    

    #------------------------------------------------------------------------------#
    # Logging
    #------------------------------------------------------------------------------#
    def log_msg(self,
                msg=None,
                label=None,
                t_constraint_elapsed=None,
                t_check_elapsed=None,
                record=None):
        # Construct the record to log.
        if record is None:
            record = OrderedDict()
        record['check_count'] = self.check_counter
        record['z3_add_elapsed_time'] = self.z3_add_elapsed_time
        self.z3_add_elapsed_time = 0.0
        if msg is not None:
            record['msg'] = msg
        if label is not None:
            record['label'] = ' -> '.join(list(OrderedDict.fromkeys(self.tag_stack)))
        if t_constraint_elapsed is not None:
            record['construct_time'] = t_constraint_elapsed
        if t_check_elapsed is not None:
            record['check_time'] = t_check_elapsed
            record['total_elapsed'] = self.total_construct_elapsed_time + self.total_check_elapsed_time
        if self.log_fn is not None:
            self.log_fn(**record)
        sys.stdout.flush()


    @contextmanager
    def group(self, tag=None, check_model=False):
        """Groups related constraints, then adds them to the solver.

        This context manager ...
        """
        
        if tag is None:
            tag = self.tag_stack[-1]
        self.tag_stack.append(tag)
        t_construct_start = time.time()
        yield
        t_construct_elapsed = time.time() - t_construct_start
        self.total_construct_elapsed_time += t_construct_elapsed
        t_check_elapsed = None
        if check_model:
            _, t_check_elapsed = self.check()
            sys.stdout.flush()
            tag = ''
            self.log_msg(label=tag,
                         t_constraint_elapsed=t_construct_elapsed,
                         t_check_elapsed=t_check_elapsed)
        self.tag_stack.pop()

    #------------------------------------------------------------------------------#
    # Optimization
    #------------------------------------------------------------------------------#

    def linear_search_for_minimum(self,
                                  bottom,
                                  top,
                                  pred,
                                  timeout='infty',
                                  verbose=False,
                                  callback=None):
        """Optimzation procedure that searches over a specified range.

        The first call to this method will have an infinite timeout, and
        later (recursive) calls will have a finite timeout; however
        during over-generation detection (after priming the optimization
        stack), the method should always be called with a finite
        timeout.
        """

        if bottom > top:
            self.log_msg(msg=f"bottom ({bottom}) > top ({top}), so now top = bottom.")
            top = bottom

        assert bottom <= top, (bottom, top)
        if verbose:
            self.log_msg(msg="%s: bottom: %d, top: %d"%(pred.__name__, bottom, top))
        p = Bool('linear_search_min_%s_%d'%(pred.__name__, top))
        self.solver.add(Implies(p, pred(top)))

        if timeout:
            self.set_timeout(timeout=timeout)
        result, _ = self.check(constraint=p,
                               raise_exception_if_not_satisfiable=False)
        if timeout:
            self.set_timeout(timeout='infty')

        self.log_msg(msg=f"Solver Result: {result}, {type(result)}")
        if str(result) == 'sat':
            # Re-run successful check locally so that it can be used to speed
            # up the other checks.
            local_result, _ = self.check(constraint=p,
                                         raise_exception_if_not_satisfiable=False)
            
            if bottom == top:
                return top
            try:
                assert local_result == result, (str(local_result), str(result))
                next_top = top - 1
                
                # if callback != None:
                #     callback_value = callback()
                #     print(f"callback_value: {callback_value}; type: {type(callback_value)}")
                #     if callback_value < next_top:
                #         next_top = callback_value
                #     if bottom > next_top:
                #         next_top = bottom

                next_timeout = SMTSolver.OPTIMIZATION_TIMEOUT_MILLISECONDS
                return self.linear_search_for_minimum(bottom,
                                                      next_top,
                                                      pred,
                                                      verbose=verbose,
                                                      timeout=next_timeout,
                                                      callback=callback)
            except:
                traceback.print_exc()
                return top
        raise Exception(f"Could not find any satisfying value in search-range; result: {result}")
