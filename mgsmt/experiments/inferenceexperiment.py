#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#
import collections, copy, itertools, os, pathlib, pprint as pp, random, shutil
import subprocess, sys, time, traceback, uuid
import simplejson as json

import z3

import mgsmt
import mgsmt.experiments
import mgsmt.experiments.experiment as experiment
import mgsmt.grammar.optimization

#------------------------------------------------------------------------------#


class InferenceExperiment(experiment.Experiment):

    def get_blocking_constraints(self, ogd_experiment_results):
        # For now, randomly pick a derivation and its associated blocking
        # constraint; later we will process multiple derivations in parallel.
        for df_id, blocking_constraints in random.sample(ogd_experiment_results.items(),
                                                         k=len(ogd_experiment_results)):
            self.log(msg=f"Processing DF_id: {df_id} with {len(blocking_constraints)} blocking constraints.")
            if blocking_constraints:
                yield blocking_constraints


    def overgeneration_tests(self):
        # TODO: The topological sort currently used should be replaced by a
        # domination matrix.
        def get_ic(df_id):
            for ic in self.interface_conditions:
                if self.grammar.ic2df[ic.label] == df_id:
                    return ic
            else:
                assert False
        
        def get_params(df_id, entries):
            new_params = copy.deepcopy(self.backup_of_params)
            new_params['initial_lexical_items'] = self.output['per_dm_lexicons'][df_id]
            new_params['input_sequence'] = [entries[0]['constraint']]
            new_params['ics_to_use'] = "0"
            new_params['init_from_lexicon'] = True
            json_norm = lambda x: json.loads(json.dumps(x))
            nlc = [{'lexical_entry': json_norm(entry['lexical_entry']),
                    'proj_child': {k:json_norm(v) for k, v in entry['proj_child'].items()},
                    'nproj_child': {k:json_norm(v) for k, v in entry['nproj_child'].items()},
                    'constraint': entry['constraint']}
                   for entry in entries]
            new_params['negative_locality_constraints'] = nlc
            return new_params

        ic_probes = self.grammar.ic_probes
        return {df_id: get_params(df_id, [entry for _, entry in ic_probes[df_id].items()])
                for df_id in sorted(self.grammar.derivation_models.keys())
                if not get_ic(df_id).is_structure_with_embedding()}


    def update_wisdom_history(self):
        wisdom = json.loads(self.optstack.json())
        self.log(msg="Wisdom:")
        pp.pprint(wisdom)
        self.wisdom_history.append(wisdom)


    def constrain_grammar(self, ogd_experiment_results):
        # Constrain the grammar with blocking constraints that will rule out
        # overgenerations.
        for blocking_constraints in self.get_blocking_constraints(ogd_experiment_results):
            try:
                for bc in blocking_constraints:
                    if bc in self.optstack.enum_all_blocking_constraints_in_stack():
                        raise mgsmt.grammar.optimization.RedundantBlockingConstraintException(bc)
                    print(bc)
                    if bc['intruder']['str_repr'] == bc['proj_child']['str_repr']:
                        raise mgsmt.grammar.optimization.InvalidBlockingConstraintException(bc)
                self.optstack.add_constraints(blocking_constraints)
                self.update_wisdom_history()
                return False
            except mgsmt.grammar.optimization.RedundantBlockingConstraintException as rbce:
                print(rbce)
                continue
            except mgsmt.grammar.optimization.InvalidBlockingConstraintException as ibce:
                print(ibce)
                continue
            except:
                raise
        else:
            self.log(msg="No overgenerations detected.")

        return True


    def extract_lexicon(self):
        final_lexicon, per_dm_lexicons = self.grammar.extract_lexicon()
        self.output['final_lexicon'] = final_lexicon
        self.output['per_dm_lexicons'] = per_dm_lexicons


    def load_model_values(self):
        mv_fp = self.params.get('model_values_loading_filepath', None)
        model_values = {}
        if mv_fp:
            with open(mv_fp, 'r') as f_in:
                model_values = json.load(f_in)
        return model_values


    def serialize_model_values(self):
        # Read model values.
        model_values = self.grammar.serialize_derivation_model_values()
        # Serialize model values.
        mv_fp = self.params.get('model_values_serialization_filepath', None)
        if mv_fp:
            with open(mv_fp, 'w') as f_out:
                json.dump(model_values, f_out)
                self.log(msg=f"Serialized derivation model values to: {mv_fp}")


    def run(self):
        self.log(msg=z3.get_version_string())
        self.ogd_experiment_results_history = []
        self.wisdom_history = []

        try:
            self.initialize_model()
            model_values = self.load_model_values()
            # Todo: "include_pf_constraints" should be refactored to "constrain_pf"
            self.constrain_model_with_input_sequence(
                include_locality_constraints=self.params['enforce_LF_interface_conditions'],
                include_sent_type_constraint=self.params['enforce_LF_interface_conditions'],
                include_categorical_constraints=self.params['enforce_LF_interface_conditions'],
                include_pf_constraints=self.params['enforce_PF_interface_conditions'],
                alternating_ic_mode=self.params['alternate_enforcement_of_interface_conditions'],
                model_values=model_values)
            self.log(msg="Model initialized.")
            self.optstack.prime_stack(wisdom=self.params['wisdom'])
            self.update_wisdom_history()
            self.serialize_model_values()

            while True:
                self.extract_lexicon()
                # Detect over-generations.
                ogd_experiment_results = yield self.overgeneration_tests()
                self.ogd_experiment_results_history.append(ogd_experiment_results)
                if self.constrain_grammar(ogd_experiment_results):
                    break

            self.extract_lexicon()
            if self.params['display.jupyter-widgets']:
                self.create_final_report(output_dir=self.logging_summary_dir)
        except GeneratorExit:
            self.log(msg="Exiting the inference procedure.")
        except:
            self.log(msg="Encountered an exception while running the experiment.")
            traceback.print_exc()
            raise
        finally:
            self.log(msg=f"Wisdom History: {len(self.wisdom_history)}.")
            self.log(msg=f"OvergenerationDetection Results: {len(self.ogd_experiment_results_history)}.")
            shutil.copy(self.config_filename, self.logging_summary_dir)
            self.log(msg="End of program.")
            self.log_file.close()
            if self.params['display.jupyter-widgets']:
                shutil.copy(self.log_file.name, self.logging_summary_dir)
            #return self.output
