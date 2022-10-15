#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import collections, copy, itertools, os, pathlib, pprint as pp, random, shutil
import subprocess, sys, time, traceback, uuid
import simplejson as json

from z3 import And, Or, Not, Implies, Xor, Distinct, If, PbEq, PbGe, PbLe

import mgsmt
import mgsmt.experiments, mgsmt.grammar
import mgsmt.experiments.experiment as experiment
import mgsmt.grammar.interfacecondition as interfacecondition

class OvergenerationDetectionExperiment(experiment.Experiment):


    def run(self):
        try:
            # Initialize the model with a pre-specified lexicon.
            self.initialize_model(init_lexicon_from_spec=True)

            # TODO: Debug the probibit-idle-entries.
            #self.grammar.lexicon_formula.prohibit_idle_entries()

            # Add a derivation with no positive locality interface conditions applied.
            self.constrain_model_with_input_sequence(include_locality_constraints=False,
                                                     include_pf_constraints=False)

            # Check the model (i.e. run the bottom up parser on the lexicon); if the model
            # is not satisfiable, then exit with an error.
            self.grammar.evaluate()
            final_lexicon, per_dm_lexicons = self.grammar.extract_lexicon()

            # Detect overgenerations.
            for idx_entry, entry in enumerate(self.params['negative_locality_constraints']):
                # Push the negative locality constraint onto the solver stack.
                self.log(msg="[OGD] Pushing the solver.")
                self.solver.solver.push()

                self.log(msg=f"Testing probe #{idx_entry}.")
                ic = interfacecondition.InterfaceCondition.construct_ic(entry['constraint'], self.params)
                df_id = self.grammar.ic2df[self.interface_conditions[0].label]
                df = self.grammar.derivation_formulas[df_id]
                lf = self.grammar.lexicon_formula
                bus = lf.derivations[df_id]['bus']
                lc = ic.constraints['structural']['locality']
                arg_label = entry['constraint'].get('arg_label', None)
                ic.add_negative_locality_constraints(df, arg_label=arg_label, locality_constraints=lc)

                # Check the model; if it is not satisfiable, return the
                # associated lexical entry to prohibit.
                try:
                    self.grammar.evaluate()
                    self.log(msg="Overgeneration detected.")

                    # Identify the derivation-formula node for the non-proj lexical-entry.
                    np_le = entry['nproj_child']['lexical_entry']
                    np_le = json.dumps({'cat': np_le['cat'],
                                        'pf': np_le['pfs'][0],
                                        'sfs': np_le['features']})
                    assert np_le in lf.init_spec_jsle_to_lfle, (np_le, lf.init_spec_jsle_to_lfle.keys())
                    np_f_idx = entry['nproj_child']['feature_index']
                    non_proj_node = lf.init_spec_jsle_to_lfle[np_le].nodes[np_f_idx]

                    # Identify the lexical entry and feature index of the
                    # structure that wrongly merges with the non-proj lexical
                    # entry.
                    dm = self.grammar.derivation_models[df_id]
                    lm = self.grammar.lexicon_model
                    m_eval = dm.model.evaluate

                    def locate_dnode(lnode):
                        for dnode in df.nodes():
                            if m_eval(And(dnode != df.null_node, bus(dnode) == lnode)):
                                return dnode
                        else:
                            return None

                    np_dnode = locate_dnode(non_proj_node)
                    xyz = next((x for x in df.nodes() if m_eval(And(x != df.null_node,
                                                                    bus(x) == non_proj_node))),
                               None)

                    if not(m_eval(np_dnode == xyz)):
                        self.log(msg="Catastrophic failure. Mission aborted.")
                        sys.exit()

                    assert np_dnode != None
                    intruder_lexical_entry, intruder_feature_index = None, None

                    result = {'lexical_entry': entry['lexical_entry'],
                              'proj_child': entry['proj_child'],
                              'nproj_child': entry['nproj_child']}

                    for intruder_dnode in df.nodes():
                        term = And(np_dnode != intruder_dnode,
                                   df.merged(np_dnode, intruder_dnode) == df.parent(intruder_dnode),
                                   df.head(intruder_dnode) != df.null_node)
                        if m_eval(term):
                            (intruder_le, intruder_f_idx) = dm.get_indexed_lexical_entry(intruder_dnode, lm)
                            result['intruder'] = {'lexical_entry': intruder_le,
                                                  'feature_index': intruder_f_idx,
                                                  'str_repr': dm.get_lex_entry_str(intruder_dnode, lm, HTML=False)}
                            break
                    else:
                        sys.exit()

                    if self.params['display.jupyter-widgets']:
                        self._visualize(label='boom')
                        self.serialize_images(label='boom')
                    self.log(msg=f"Overgeneration Detector returning lex. entry: {result}")
                    return [result]
                except mgsmt.solver.SMTSolverException:
                    self.log(msg="No overgeneration detected; testing the next IC.")
                    traceback.print_exc()
                    continue
                except:
                    traceback.print_exc()
                    sys.exit()
                    raise
                finally:
                    self.log(msg="[OGD] Popping the solver.")
                    self.solver.solver.pop()
            else:
                return []

        except:
            self.log(msg="Encountered an exception while running the experiment.")
            traceback.print_exc()
            raise
