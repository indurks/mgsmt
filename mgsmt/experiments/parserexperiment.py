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
import mgsmt.experiments, mgsmt.grammar, mgsmt.formulas
import mgsmt.formulas.pfinterfaceformula
import mgsmt.experiments.experiment as experiment
import mgsmt.grammar.interfacecondition as interfacecondition


def construct_parser_experiment_configurations(initial_lexicon,
                                               base_params,
                                               evaluation_corpus,
                                               extra_lexical_items=None):
    """Construct experiment configurations from an evaluation corpus.
    """

    def relevant_phonological_forms(input_sequence):
        covert_pforms = [mgsmt.formulas.pfinterfaceformula.PFInterfaceFormula.EPSILON]
        overt_pforms = [overt_pform 
                        for entry in input_sequence
                        for overt_pform in entry['sentence'].split()
                        if overt_pform not in ('.', '?')]
        return overt_pforms + covert_pforms


    def get_params(input_sequence):
        new_params = copy.deepcopy(base_params)

        relevant_lexical_items = relevant_phonological_forms(input_sequence)
        new_params['initial_lexical_items'] = copy.deepcopy(initial_lexicon)

        if extra_lexical_items:
            for lex_item in extra_lexical_items:
                new_params['initial_lexical_items'].append(lex_item)

        new_params['initial_lexical_items'] = [lex_entry
                                               for lex_entry in new_params['initial_lexical_items']
                                               if lex_entry['pf'] in relevant_lexical_items]
        new_params['initial_lexical_items'] = json.dumps(new_params['initial_lexical_items'])
        new_params['input_sequence'] = input_sequence
        new_params['ics_to_use'] = "0"
        new_params['init_from_lexicon'] = True
        return new_params

    return [get_params([entry]) for entry in evaluation_corpus]


class ParserExperiment(experiment.Experiment):

    """Parse sentences with a specified MG lexicon.

    Input is an experiment-configuration JSON object that contains:
    (i) a lexicon;
    (ii) an input-sequence with a single element;
    (iii) the number of additional lexical items allowed for handling
    OOV terms;
    (iv) two boolean parameters indicating whether or not to include
    constraints associated with the PF and LF (locality based) interface
    conditions respectively.

    Output is a JSON object containing:
    (i) an integer value indicating the number of distinct parses that
    were found for the supplied annotated sentence;
    (ii) for each distinct parse, the subset of the supplied lexicon
    used to parse the supplied sentence (an empty list if no parse
    exists), and any new lexical items that were inferred for OOV
    terms.
    """


    def run(self, include_LF_constraints, include_PF_constraints, extract_all_parses=False):
        try:
            # Initialize the model with a pre-specified lexicon.
            self.initialize_model(init_lexicon_from_spec=True)

            # Add a derivation with no positive locality interface conditions
            # applied.
            self.constrain_model_with_input_sequence(include_locality_constraints=include_LF_constraints,
                                                     include_pf_constraints=include_PF_constraints,
                                                     include_categorical_constraints=include_LF_constraints,
                                                     include_sent_type_constraint=include_LF_constraints)

            # Check the model (i.e. run the bottom up parser on the lexicon);
            # if the model is not satisfiable, then exit with an error.
            self.grammar.evaluate()
            #final_lexicon, per_dm_lexicons = self.grammar.extract_lexicon()

            if not(extract_all_parses):
                if self.params['display.jupyter-widgets']:
                    self._visualize(label='parser-experiment')
                    #self.serialize_images(label='parser-experiment')
            else:
                assert len(self.grammar.derivation_formulas) == 1
                df = [df for df in self.grammar.derivation_formulas.values()][0]
                lf = self.grammar.lexicon_formula
                for i, (lm, dm) in enumerate(self.grammar.evaluate_extract_all_parses(parser_lexicon_formula=lf,
                                                                                      parser_derivation_formula=df),
                                             start=1):
                    self.log(msg=f"Displaying Parse #{i}.")
                    self.grammar.lexicon_model = lm
                    self.grammar.derivation_models = {0: dm}
                    self._visualize(label='parser-experiment')
            
            return {'status': 'success'}
        except:
            msg = "Encountered an exception while running the experiment."
            self.log(msg=msg)
            traceback.print_exc()
            return {'status': 'failure', 'exception_msg': msg}
