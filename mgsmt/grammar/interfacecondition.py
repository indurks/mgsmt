#!/usr/bin/env python3
# -*- coding: utf-8 -*-


__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import json, uuid

from z3 import *

import mgsmt
import mgsmt.solver, mgsmt.formulas

from mgsmt.formulas.derivationformula import DerivationFormula

#------------------------------------------------------------------------------#

class InterfaceCondition:
    ic_labels = set()

    def __init__(self,
                 label,
                 num_words,
                 max_num_empty_lexical_items,
                 max_num_movements,
                 max_num_head_movements,
                 max_num_features_per_lexical_entry,
                 description=None,
                 original_json_data=None):
        assert label not in InterfaceCondition.ic_labels
        InterfaceCondition.ic_labels.add(label)
        self.label = label
        self.num_words = num_words
        self.max_num_empty_lexical_items = max_num_empty_lexical_items
        self.max_num_movements = max_num_movements
        self.max_num_head_movements = max_num_head_movements
        self.max_num_features_per_lexical_entry = max_num_features_per_lexical_entry
        self.description = description
        self.constraints = {'surface': None,
                            'structural': {'locality': [],
                                           'sent_type': None,
                                           'categorical': None}}
        self.original_json_data = original_json_data


    def tokens(self):
        return self.constraints['surface']

    def get_sentence(self):
        tkns = self.constraints['surface']
        sent_type = self.constraints['structural']['sent_type']
        punc = '.' if sent_type == 'declarative' else '?'
        return ' '.join(tkns) + punc

    def set_surface_forms(self, surface_forms):
        assert all(isinstance(pf, str) for pf in surface_forms)
        assert len(surface_forms) == self.num_words
        self.constraints['surface'] = surface_forms

    def add_categorical_constraints(self, categorical_constraints):
        self.constraints['structural']['categorical'] = categorical_constraints

    def add_locality_constraint(self, lc_type, lc_args):
        assert (lc_type, lc_args) not in self.constraints['structural']['locality']
        self.constraints['structural']['locality'].append((lc_type, lc_args))

    def add_derivation_head_constraint(self, sent_type):
        self.constraints['structural']['sent_type'] = sent_type

    def is_structure_with_embedding(self):
        """
        Check for the presence of two or more predicates in theta-matrices.
        """
        return 1 < sum([1 for x, _ in self.constraints['structural']['locality']
                        if x == 'theta'])
            
    
    def get_derivation_formula(self,
                               solver,
                               pfi,
                               lexicon_formula=None,
                               include_locality_constraints=True,
                               include_sent_type_constraint=True,
                               include_categorical_constraints=True,
                               include_pf_constraints=True):
        assert isinstance(solver, mgsmt.solver.smtsolver.SMTSolver)
        assert isinstance(pfi, mgsmt.formulas.pfinterfaceformula.PFInterfaceFormula)
        #1 < sum([1 for x, _ in self.constraints['structural']['locality'] if x == 'theta'])
        should_boost = self.is_structure_with_embedding()
        hd_mv_boost = 2 if should_boost else 0
        empty_lex_items_boost = 2 if should_boost else 0
        max_num_mv_boost = 2 if should_boost else 0
        if should_boost:
            solver.log_msg(msg='Boosting the number of empty lexical items.')
        df = DerivationFormula(solver,
                               pfi,
                               NUM_WORDS=self.num_words,
                               MAX_NUM_EMPTY_LEXICAL_ITEMS=self.max_num_empty_lexical_items + empty_lex_items_boost,
                               MAX_NUM_MOVEMENTS=self.max_num_movements + max_num_mv_boost,
                               MAX_NUM_HEAD_MOVEMENTS=self.max_num_head_movements + hd_mv_boost,
                               MAX_NUM_FEATURES_PER_LEXICAL_ENTRY=self.max_num_features_per_lexical_entry,
                               whitelisted_surface_forms=[self.constraints['surface']],
                               lexicon_formula=lexicon_formula,
                               include_precedence_relations=include_pf_constraints)

        # Optionally include LF interface conditions.
        locality_constraints = self.constraints['structural']['locality'] if include_locality_constraints else None
        sent_type_constraint = self.constraints['structural']['sent_type'] if include_sent_type_constraint else None
        categorical_constraints = self.constraints['structural']['categorical'] if include_categorical_constraints else None

        # Optionally include PF interface conditions.
        tokens = self.tokens() if include_pf_constraints else None

        solver.log_msg(msg=f"Including Locality Constraints: {locality_constraints is not None}.")
        solver.log_msg(msg=f"Including Sent. Type Constraint: {sent_type_constraint is not None}.")
        solver.log_msg(msg=f"Including Categorical Constraints: {categorical_constraints is not None}.")
        solver.log_msg(msg=f"Including PF (linearization) Constraints: {tokens is not None}.")
        
        df.add_ic_constraints(locality_constraints=locality_constraints,
                              sent_type_constraint=sent_type_constraint,
                              categorical_constraints=categorical_constraints,
                              tokens=tokens)
        df.add_UG_constraints()
        return df


    def add_negative_locality_constraints(self, derivation_formula, locality_constraints=None, arg_label=None):
        df = derivation_formula
        if not locality_constraints:
            locality_constraints = self.constraints['structural']['locality']
        df.add_negative_locality_constraints(locality_constraints, arg_label)


    def json_repr(self):
        data = {'PF': self.constraints['surface'],
                'LF': {'Locality': list(self.constraints['structural']['locality']),
                       'Sentence Type': self.constraints['structural']['sent_type']}}
        return json.dumps(data, ensure_ascii=False)


    def construct_ic(data, params):
        tokens = data['sentence'].strip().split()[:-1]
        #assert len(tokens) == len(set(tokens)), 'Duplicate token in: "%s"'%(data['sentence'])

        # Create the interface condition.
        ic = InterfaceCondition(
            label=str(uuid.uuid4()),
            num_words=len(tokens),
            max_num_empty_lexical_items=params['max_num_empty_lexical_items'],
            max_num_movements=params['max_num_movements'],
            max_num_head_movements=params['max_num_head_movements'],
            max_num_features_per_lexical_entry=params['max_num_features_per_lexical_entry'],
            original_json_data = copy.deepcopy(data)
        )

        # Add constraints for the surface (phonological) forms.
        ic.set_surface_forms(tuple(tokens))

        def indexed_forms(tokens, words):
            return tuple([tuple([w, tokens.index(w)]) for w in words])

        # Add constraints for the categories associated with specified phrases.
        if 'categorical_constraints' in data:
            ic.add_categorical_constraints({k:indexed_forms(tokens, ws)
                                            for k, ws in data['categorical_constraints'].items()})

        # Add constraints for the type of sentence, inferred by end-of-sentence
        # punctuation.
        if data['sentence'].endswith('.'):
            ic.add_derivation_head_constraint('declarative')
        elif data['sentence'].endswith('?'):
            ic.add_derivation_head_constraint('question')
        else:
            assert False, 'Could not recognize the type of this sentence: "%s"'%(data['sentence'])

        if len(tokens) != len(set(tokens)):
            return ic

        # Add constraints for (local) syntactic relations.
        for lc_type, lc_args in data['locality_constraints']:
            ic.add_locality_constraint(lc_type,
                                       {k:indexed_forms(tokens, v.split())
                                        for k, v in lc_args.items()})

        return ic
