#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#
import simplejson as json, uuid
import z3
from z3 import And, Or, Not, Implies, Xor, Distinct, If, PbEq, PbGe, PbLe

import mgsmt.solver
#------------------------------------------------------------------------------#


class RedundantBlockingConstraintException(Exception):

    def __init__(self, blocking_constraint):
        self.blocking_constraint = blocking_constraint

    def __str__(self):
        return "[RedundantBlockingConstraintException] " + str(self.blocking_constraint)


class InvalidBlockingConstraintException(Exception):

    def __init__(self, blocking_constraint):
        self.blocking_constraint = blocking_constraint

    def __str__(self):
        return "[InvalidBlockingConstraintException] " + str(self.blocking_constraint)


class OptimizationStack(object):

    def __init__(self,
                 grammar,
                 json_repr=None,
                 filename=None,
                 visualization_callback=None,
                 verbose=False):
        self.grammar = grammar
        self.verbose = verbose
        self.visualization_callback = visualization_callback

        opt_preds = (self.optimize_base,
                     self.minimize_num_lexical_entries,
                     self.minimize_num_features_in_lexicon,
                     self.minimize_num_derivation_nodes,
                     self.minimize_num_distinct_selectional_features)
        self.stack = [{'label': pred.__name__,
                       'level': level,
                       'pred': pred,
                       'constraints': [],
                       'min_value': None}
                      for level, pred in enumerate(opt_preds)]

        if filename:
            raise NotImplemented


    def extract_optimization_metrics(self, verbose=False):
        s = self.grammar.solver
        assert s.model != None
        values = {tag:int(s.model[var].as_long())
                  for tag, var in self.optimization_indicator_vars.items()}
        if verbose:
            for tag, value in values.items():
                s.log_msg(msg=f"[OptimizationMetrics] tag: {tag}; value: {value}.")
        return values


    def initialize_optimization_indicator_variables(self):
        self.optimization_indicator_vars = oiv = {}
        self.optimization_indicator_terms = oit = {}
        
        for tag in ('num_lexical_items',
                    'num_lexical_feats',
                    'num_derivation_feats',
                    'num_selectional_feats'):
            oiv[tag] = z3.Int(f'int_indicator_uuid{uuid.uuid4().int}_{tag}')
            oit[tag] = self.grammar.get_metric_term(tag=tag)

            # Construct a pseudo-boolean equaliy and add to the solver.
            s = self.grammar.solver
            with s.group(tag=f"Adding a pseudo-boolean equality for the optimization metric: {tag}."):
                assert all([w == 1 for _, w in oit[tag]]), oit[tag]
                sum_term = z3.Sum([z3.If(t, 1, 0) for t, _ in oit[tag]])
                s.add_singleton(sum_term == oiv[tag])


    def prime_stack(self, wisdom=None):
        """
        This method assumes that the optimization stack has not been
        initialized, and proceeds to apply the optimization constraints
        and blocking constraints associated with each layer of the
        stack. After this method is executed, the system expects that
        the optimization stack will be used by calling the
        add_constraints method to apply additional blocking constraints.
        """
        s = self.grammar.solver
        self.initialize_optimization_indicator_variables()
        
        wisdom_map = {}
        if wisdom:
            wisdom_map = {layer['level']:layer for layer in wisdom}
            s.log_msg(f"OptStack: priming the stack with pre-supplied wisdom.")

        for layer in self.stack:
            w_layer = wisdom_map.get(layer['level'], None)
            s.solver.push()
            if w_layer == None:
                layer['min_value'] = layer['pred']()
            else:
                assert w_layer['level'] == layer['level'], (w_layer['level'], layer['level'])
                assert w_layer['label'] == layer['label'], (w_layer, layer)
                layer['min_value'] = layer['pred'](bottom=w_layer['min_value'], short_circuit=True)
                if len(w_layer['constraints']) > 0:
                    raise NotImplemented # Need to verify this works for doublet constraints.
                self.add_constraints(w_layer['constraints'], level=w_layer['level'])
            s.log_msg(f"OptStack[level: {layer['level']}]: level primed with wisdom.")


    def _get_ptr(self):
        k = len(self.stack) - 1
        for i in range(k):
            if self.stack[k-i]['min_value']:
                return k-i
        else:
            return 0


    def _cur_frame(self):
        return self.stack[self._get_ptr()]


    def add_constraints(self, lexical_entries, level=4):
        """
        This method assumes the optimization stack has been primed; the 
        method will apply each of the blocking constraints stored in 
        lexical_entries.
        """
        s = self.grammar.solver
        cf = self._cur_frame()
        assert cf['level'] == level, (cf['level'], level)

        try:
            # TODO: the following for-loop should check against constraints in
            # all levels of the optimization stack below and including the
            # current level.
            for lex_entry in lexical_entries:
                if lex_entry in cf['constraints']:
                    raise RedundantBlockingConstraintException(lex_entry)
            cf['constraints'].extend(lexical_entries)
            if cf['level'] > 0:
                self.grammar.solver.set_timeout(timeout=mgsmt.solver.SMTSolver.OPTIMIZATION_TIMEOUT_MILLISECONDS)
            else:
                self.grammar.solver.set_timeout(timeout='infty')
            for lex_entry in lexical_entries:
                self.grammar.add_blocking_constraint(lex_entry)
            self.grammar.evaluate()
            self.extract_optimization_metrics(verbose=True)
            self.grammar.solver.set_timeout(timeout='infty')
            s.log_msg(f"OptStack[level: {level}]: added {len(lexical_entries)} blocking constraints.")
            return True
        except mgsmt.solver.SMTSolverException:
            s.log_msg(f"OptStack[level: {level}]: unsatisfiable model.")
            self.grammar.solver.set_timeout(timeout='infty')
            if cf['level'] == 0:
                raise NotImplemented
            else:
                entries = [c for c in cf['constraints']]
                cf['constraints'].clear()
                prior_min_value = cf['min_value']
                cf['min_value'] = None
                s.log_msg(f"OptStack[level: {level}]: popping the stack.")
                s.solver.pop()
                ac_result = self.add_constraints(entries, level=level-1)
                s.log_msg(f"OptStack[level: {level}]: pushing the stack.")
                s.solver.push()
                # No point trying the prior minimum value, which we know was unsatisfiable.
                if ac_result:
                    cf['min_value'] = cf['pred'](bottom=prior_min_value + 1)
                else:
                    cf['min_value'] = cf['pred']()
                s.log_msg(f"OptStack[level: {level}]: minimum value: {cf['min_value']}")
                return False
        except:
            raise
        finally:
            self.grammar.solver.set_timeout(timeout='infty')


    def enum_all_blocking_constraints_in_stack(self):
        return [constraints
                for layer in self.stack
                for constraints in layer['constraints']]


    def defragment(self):
        raise NotImplemented


    def __str__(self):
        raise NotImplemented


    def json(self):
        return json.dumps([{k:v for k, v in layer.items() if k != 'pred'}
                           for layer in self.stack])


    def latex(self):
        raise NotImplemented


    def optimize_base(self, bottom=None, short_circuit=None):
        s = self.grammar.solver
        if self.verbose:
            s.log_msg('Ensuring selectional features are used in order and without gaps.')
        self.grammar.impose_ordered_selectional_features_constraint()

        if self.verbose:
            s.log_msg('Ensuring licensing features are used in order and without gaps.')
        self.grammar.impose_ordered_licensing_features_constraint()

        self.grammar.evaluate()
        return True


    def get_max_num_active_lexicon_nodes(self):
        return self.grammar.lexicon_formula.num_lexicon_nodes


    def get_max_num_lexicon_entries(self):
        lf = self.grammar.lexicon_formula
        num_entries = len(lf.entries)
        return num_entries


    def get_callback(self, tag):
        def callback():
            s = self.grammar.solver
            s.model = s.solver.model()
            values = self.extract_optimization_metrics(verbose=True)
            return values[tag]
        return callback


    def minimize_num_lexical_entries(self,
                                     bottom=1,
                                     short_circuit=False):
        s = self.grammar.solver
        if self.verbose:
            s.log_msg(msg="Minimizing the number of entries in the lexicon.")

        # Scan for the minimum value.
        self.grammar.solver.set_timeout(timeout=mgsmt.solver.SMTSolver.OPTIMIZATION_TIMEOUT_MILLISECONDS)
        top = self.get_max_num_lexicon_entries()

        callback = self.get_callback('num_lexical_items')
        # callback_value = callback()
        # top = callback_value if callback_value < top else top
        
        pred = self.grammar.minimize_num_lexical_items
        if short_circuit:
            min_value = bottom
        else:
            min_value = s.linear_search_for_minimum(bottom=bottom,
                                                    top=top,
                                                    pred=pred,
                                                    verbose=self.verbose,
                                                    callback=callback)
        s.log_msg(f"Minimum number of lexical items: {min_value}; short_circuit={short_circuit}")

        # Enforce the minimum.
        self.grammar.solver.set_timeout(timeout='infty')
        with s.group(tag="Minimize the number of Lexical Items."):
            s.add_singleton(self.grammar.minimize_num_lexical_items(min_value))
        self.grammar.evaluate()
        self.extract_optimization_metrics(verbose=True)

        self.visualization_callback(label='min-num-lex-entries')
        return min_value


    def minimize_num_features_in_lexicon(self,
                                         bottom=1,
                                         short_circuit=False):
        s = self.grammar.solver
        if self.verbose:
            s.log_msg('Minimizing the number of syntactic features in the lexicon.')

        # Scan for the minimum value.
        self.grammar.solver.set_timeout(timeout=mgsmt.solver.SMTSolver.OPTIMIZATION_TIMEOUT_MILLISECONDS)
        top = self.get_max_num_active_lexicon_nodes()

        callback = self.get_callback('num_lexical_feats')
        # callback_value = callback()
        # top = callback_value if callback_value < top else top
        
        pred = self.grammar.minimize_num_features
        if short_circuit:
            min_value = bottom
        else:
            try:
                min_value = s.linear_search_for_minimum(bottom=bottom,
                                                        top=top,
                                                        pred=pred,
                                                        verbose=self.verbose,
                                                        callback=callback)
            except:
                import sys, traceback
                traceback.printexc()
                sys.exit()
        s.log_msg(f"Minimum number of features: {min_value}; short_circuit={short_circuit}")

        # Enforce the minimum.
        self.grammar.solver.set_timeout(timeout='infty')
        with s.group(tag="Minimize the total number of syntactic features in the lexicon."):
            s.add_singleton(self.grammar.minimize_num_features(min_value))
        self.grammar.evaluate()
        self.extract_optimization_metrics(verbose=True)

        self.visualization_callback(label='min-total-num-syn-feats-in-lex')
        return min_value


    def minimize_num_derivation_nodes(self,
                                      bottom=1,
                                      short_circuit=False):
        s = self.grammar.solver
        if self.verbose:
            s.log_msg('Minimizing the total number of derivation nodes.')

        # Scan for the minimum value.
        self.grammar.solver.set_timeout(timeout=mgsmt.solver.SMTSolver.OPTIMIZATION_TIMEOUT_MILLISECONDS)
        dfs = self.grammar.derivation_formulas
        top = sum([len(list(df.nodes())) for df_id, df in dfs.items()])

        callback = self.get_callback('num_derivation_feats')
        # callback_value = callback()
        # top = callback_value if callback_value < top else top

        pred = self.grammar.minimize_num_derivation_nodes
        if short_circuit:
            min_value = bottom
        else:
            min_value = s.linear_search_for_minimum(bottom=bottom,
                                                    top=top,
                                                    pred=pred,
                                                    verbose=self.verbose,
                                                    callback=callback)
        s.log_msg(f"Minimum number of derivation nodes: {min_value}; short_circuit={short_circuit}")

        # Enforce the minimum.
        self.grammar.solver.set_timeout(timeout='infty')
        with s.group(tag="Minimizing the total number of derivation nodes (across all derivations)."):
            s.add_singleton(self.grammar.minimize_num_derivation_nodes(min_value))
        self.grammar.evaluate()
        self.extract_optimization_metrics(verbose=True)

        self.visualization_callback(label='min-num-derivation-nodes')
        return min_value


    def minimize_num_distinct_selectional_features(self,
                                                   bottom=1,
                                                   short_circuit=False):
        s = self.grammar.solver
        if self.verbose:
            s.log_msg('Minimize the number of distinct selectional features in the lexicon.')

        # Scan for the minimum value.
        self.grammar.solver.set_timeout(timeout=mgsmt.solver.SMTSolver.OPTIMIZATION_TIMEOUT_MILLISECONDS)
        top = len(self.grammar.lexicon_formula.selectional_syn_feats) + 1

        callback = self.get_callback('num_selectional_feats')
        # callback_value = callback()
        # top = callback_value if callback_value < top else top

        pred = self.grammar.minimize_num_used_selectional_features
        if short_circuit:
            min_value = bottom
        else:
            min_value = s.linear_search_for_minimum(bottom=bottom,
                                                    top=top,
                                                    pred=pred,
                                                    verbose=self.verbose,
                                                    callback=callback)
        s.log_msg(f"Minimum Number of selectional features in the lexicon: {min_value}; short_circuit={short_circuit}")

        # Enforce the minimum.
        self.grammar.solver.set_timeout(timeout='infty')
        with s.group("Minimize the number of distinct selectional features appearing in the lexicon."):
            s.add_singleton(self.grammar.minimize_num_used_selectional_features(min_value))
        self.grammar.evaluate()
        self.extract_optimization_metrics(verbose=True)

        self.visualization_callback(label='min-num-distinct-selectional-feats-in-lex',
                                    visualize=True)
        return min_value
