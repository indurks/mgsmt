#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import collections, copy, itertools, pprint as pp, uuid

import z3
from z3 import And, Or, Not, Implies, Xor, Distinct, If, PbEq, PbGe, PbLe
from z3 import BoolSort

import mgsmt
import mgsmt.experiments.lexrepr
import mgsmt.solver.smtsolver
import mgsmt.models.derivationmodel
import mgsmt.models.lexiconmodel
import mgsmt.formulas.lexiconformula
import mgsmt.formulas.pfinterfaceformula
import mgsmt.formulas.df_serialization as df_serialization
import mgsmt.grammar.interfacecondition


class Grammar:

    def __init__(self, solver, pf_interface_formula, params):
        assert isinstance(solver, mgsmt.solver.smtsolver.SMTSolver)
        assert isinstance(pf_interface_formula, mgsmt.formulas.pfinterfaceformula.PFInterfaceFormula)
        self.solver = solver
        self.pfi = pf_interface_formula
        self.derivation_formulas = {}
        self.ic2df = {}
        self.params = params


    def add_interface_condition(self,
                                ic,
                                include_locality_constraints,
                                include_sent_type_constraint,
                                include_categorical_constraints,
                                include_pf_constraints):
        assert isinstance(ic, mgsmt.grammar.interfacecondition.InterfaceCondition), interface_condition
        df = ic.get_derivation_formula(self.solver,
                                       self.pfi,
                                       lexicon_formula=self.lexicon_formula,
                                       include_locality_constraints=include_locality_constraints,
                                       include_sent_type_constraint=include_sent_type_constraint,
                                       include_categorical_constraints=include_categorical_constraints,
                                       include_pf_constraints=include_pf_constraints)
        self.derivation_formulas[df.formula_name] = df
        self.ic2df[ic.label] = df.formula_name
        self.connect_derivation_to_lexicon(df.formula_name)
        self.solver.log_msg(msg="Finished Connecting Derivation to Lexicon.")


    def _init_lexicon(self, init_lex_repr=None, init_lexicon_from_spec=False, verbose=False):
        s = self.solver
        if verbose:
            s.log_msg(f"init_lexicon_from_spec: {init_lexicon_from_spec}")
        if init_lexicon_from_spec:
            self.lexicon_formula = mgsmt.formulas.lexiconformula.LexiconFormula.create_lexicon_from_spec(s,
                                                                                                         self.params['initial_lexical_items'],
                                                                                                         self.pfi,
                                                                                                         self.params)
        else:
            self.lexicon_formula = mgsmt.formulas.lexiconformula.LexiconFormula.create_lexicon(s,
                                                                                               self.pfi,
                                                                                               self.params)
        if verbose:
            s.log_msg('Initialized the Lexicon.')
        if init_lex_repr:
            init_lex_repr.impose_constraints_lexicon(self.lexicon_formula)
            if verbose:
                s.log_msg("Imposed constraints on the lexicon formula from the initial lexicon representation.")


    def evaluate(self, extract_all_parses=False):
        # Extract the model from the SMT-solver.
        self.solver.evaluate_model()
        # Construct the lexicon model.
        self.lexicon_model = mgsmt.models.lexiconmodel.LexiconModel(lexicon_formula=self.lexicon_formula,
                                                                    model=self.solver.model)
        # Construct the derivation model(s).
        self.derivation_models = collections.OrderedDict()
        self.ic_probes = collections.OrderedDict()
        for df_id, df in self.derivation_formulas.items():
            dm = mgsmt.models.derivationmodel.DerivationModel(derivation_formula=df,
                                                              model=self.solver.model)
            ic_probes = dm.localize_interface_conditions(self.lexicon_model)
            self.derivation_models[df_id] = dm
            self.ic_probes[df_id] = ic_probes

    
    def evaluate_extract_all_parses(self, parser_lexicon_formula=None, parser_derivation_formula=None):
        # Extract the satisfiable models from the SMT-solver.
        for (lm, dm) in self.solver.evaluate_extract_all_parses(parser_lexicon_formula=parser_lexicon_formula,
                                                                parser_derivation_formula=parser_derivation_formula):
            # Because the lexicon and derivation models will query the SMT model, we
            # need to visualize the derivation before proceeding to identify the next
            # parse.
            yield (lm, dm)
    

    def serialize_derivation_model_values(self):
        # Serialize each derivation
        model_values = {}
        for df_id, dm in self.derivation_models.items():
            model_values[df_id] = df_serialization.serialize_model_values(dm)
            self.solver.log_msg(msg=f"Serialized model values for derivation {df_id}.")
        return model_values
            

    def load_derivation_model_values(self, model_values):
        # Deserialize each derivation.
        for df_id, m_values in model_values.items():
            assert df_id in self.derivation_formulas, (df_id, self.derivation_formulas.keys())
            df_serialization.deserialize_model_values(self.derivation_formulas[df_id], m_values)
            self.solver.log_msg(msg=f"Loaded model values into derivation {df_id}.")


    def connect_derivation_to_lexicon(self, df_id):
        self.lexicon_formula.connect_derivation(self.derivation_formulas[df_id])


    def extract_lexicon(self, filepath=None, verbose=False):
        lr = mgsmt.experiments.lexrepr.LexRepr(lexicon_model=self.lexicon_model,
                                               derivation_models=list(self.derivation_models.values()))
        if filepath:
            lr.json(filepath)
            self.solver.log_msg(msg=f"Serialized the lexicon to disk: {filepath}")
        full_lexicon = lr.json()
        
        if verbose:
            print("Full Lexicon:")
            pp.pprint(full_lexicon)

        per_dm_lexicons = {}
        for df_id, dm in self.derivation_models.items():
            lr = mgsmt.experiments.lexrepr.LexRepr(lexicon_model=self.lexicon_model,
                                                   derivation_models=[dm])
            per_dm_lexicons[df_id] = lr.json()

        return full_lexicon, per_dm_lexicons


    def get_lr_le(self, lexical_entry):
        lex_entry = copy.deepcopy(lexical_entry)
        lr_le = mgsmt.experiments.lexrepr.LRLexEntry(pf=lex_entry['pfs'][0],
                                                     sfs=lex_entry['features'],
                                                     cat=lex_entry['cat'])
        return lr_le


    def add_singlet_blocking_constraint(self, lexical_entry):
        lr_le = self.get_lr_le(lexical_entry)
        get_cs = mgsmt.experiments.lexrepr.LexRepr._impose_constraints_lexical_entry
        with self.solver.group(tag=f"Blocking a lexical entry: {lexical_entry}"):
            self.solver.add_conj([Not(And(get_cs(self.lexicon_formula, lr_le, lf_le)))
                                  for lf_le in self.lexicon_formula.entries])


    def add_blocking_constraint(self, constraint):
        lf = self.lexicon_formula

        # Projecting child (what should have been merged with).
        p_le = constraint['proj_child']['lexical_entry']
        p_f_idx = constraint['proj_child']['feature_index']
        p_str = constraint['proj_child']['str_repr']

        # Intruder (what was merged with)
        i_le = constraint['intruder']['lexical_entry']
        i_f_idx = constraint['intruder']['feature_index']
        i_str = constraint['intruder']['str_repr']

        def obtain_ind(lf_le, json_le, f_idx):
            # entry must align with le in PF, Cat and features in type except
            # at f_idx, where it also must match in label.
            lr_le = self.get_lr_le(json_le)
            get_cs = mgsmt.experiments.lexrepr.LexRepr._impose_constraints_lexical_entry
            terms = get_cs(lf, lr_le, lf_le, constrain_sf_labels=False)
            lex_node = lf_le.nodes[f_idx]
            return (terms, lex_node)

        def prohibit_pairing(entryA, entryB):
            termsA, lex_node_a = obtain_ind(entryA, p_le, p_f_idx)
            termsB, lex_node_b = obtain_ind(entryB, i_le, i_f_idx)
            termEq = (lf.featLbl(lex_node_a) == lf.featLbl(lex_node_b))
            return Not(And(And(termsA), And(termsB), termEq))

        s = self.solver
        s.log_msg(f"Blocking. Proj. Child: {(p_str, p_f_idx)}; Intruder: {(i_str, i_f_idx)}.")
        with s.group(tag=f"Blocking. Proj. Child: {(p_str, p_f_idx)}; Intruder: {(i_str, i_f_idx)}."):
            s.add_conj([prohibit_pairing(x, y) for x, y in itertools.product(lf.entries, repeat=2)])


    #------------------------------------------------------------------------------#
    # Optimization methods
    #------------------------------------------------------------------------------#

    def impose_ordered_selectional_features_constraint(self):
        s = self.solver
        lf = self.lexicon_formula
        num_sel_feats = len(lf.selectional_feature_labels)
        if num_sel_feats > 1:
            ns = [node for entry in lf.entries for node in entry.nodes]
            sel_feats = lf.selectional_syn_feats
            with s.group(tag="Ensure sel. feats. x_0, x_1, ..., x_k are used, without gaps, for k > 0."):
                s.add_conj([Implies(Not(Or([lf.featLbl(x) == sel_feats[i] for x in ns])),
                                    Not(Or([lf.featLbl(x) == sel_feats[i+1] for x in ns])))
                            for i in range(num_sel_feats-1)])


    def impose_ordered_licensing_features_constraint(self):
        s = self.solver
        lf = self.lexicon_formula
        num_lic_feats = len(lf.licensing_feature_labels)
        if num_lic_feats > 1:
            ns = [node for entry in lf.entries for node in entry.nodes]
            lic_feats = lf.licensing_syn_feats
            with s.group(tag="Ensure lic. feats. x_0, x_1, ..., x_k are used, without gaps, for k > 0."):
                s.add_conj([Implies(Not(Or([lf.featLbl(x) == lic_feats[i] for x in ns])),
                                    Not(Or([lf.featLbl(x) == lic_feats[i+1] for x in ns])))
                            for i in range(num_lic_feats-1)])
                

    def get_metric_term(self, tag):
        """RHS of the pseudo-boolean equality anchoring the metric.
        """
        lf = self.lexicon_formula
        if tag == 'num_lexical_items':
            def get_bus(df_id):
                return lf.derivations[df_id]['bus']

            def get_subterm(lexical_entry):
                # Define "s" to be the first node in the lexical entry.
                s = lexical_entry.nodes[0]
                # The starting lex-node must be active.
                constraint_A = lf.lnodeType(s) != lf.LTypeSort.Inactive
                # The starting node must map to one of the (non-null) phonological forms.
                constraint_B = Or([lf.pf_map(s, p) for p in lf.pfInterface.non_null_nodes()])
                # The starting node must be connected to one of the derivations.
                constraint_C = Or([Or([And((get_bus(df_id))(lexical_d_node) == s,
                                           df.head(lexical_d_node) == lexical_d_node)
                                       for lexical_d_node in df.lex1nodes()])
                                   for df_id, df in self.derivation_formulas.items()])
                return And(constraint_A, constraint_B, constraint_C)

            return [(get_subterm(entry), 1) for entry in lf.entries]
        elif tag == 'num_lexical_feats':
            def get_subterm(entry, l_node):
                return And(lf.lnodeType(l_node) != lf.LTypeSort.Inactive,
                           Or([lf.pf_map(entry.nodes[0], pf_node)
                               for pf_node in lf.pfInterface.non_null_nodes()]))

            return [(get_subterm(entry, l_node), 1)
                    for entry in lf.entries
                    for l_node in entry.nodes]
        elif tag == 'num_derivation_feats':
            return [(df.head(x) != df.null_node, 1)
                    for df in self.derivation_formulas.values()
                    for x in df.nodes()]
        elif tag == 'num_selectional_feats':
            def get_subterm(sel_feat):
                return Or([And(lf.featLbl(x) == sel_feat,
                               lf.lnodeType(x) != lf.LTypeSort.Inactive)
                           for entry in lf.entries
                           for x in entry.nodes])
            
            return [(get_subterm(sel_feat), 1) for sel_feat in lf.selectional_syn_feats]
        else:
            raise Exception(f"Could not recognize the metric tag: {tag}")


    def minimize_num_lexical_items(self, k):
        # Minimize the number of lexical items.
        lf = self.lexicon_formula
        def get_bus(df_id):
            return self.lexicon_formula.derivations[df_id]['bus']

        def get_term(lexical_entry):
            # Define "s" to be the first node in the lexical entry.
            s = lexical_entry.nodes[0]
            # The starting lex-node must be active.
            constraint_A = lf.lnodeType(s) != lf.LTypeSort.Inactive
            # The starting node must map to one of the (non-null) phonological forms.
            constraint_B = Or([lf.pf_map(s, p) for p in lf.pfInterface.non_null_nodes()])
            # The starting node must be connected to one of the derivations.
            constraint_C = Or([Or([And((get_bus(df_id))(lexical_d_node) == s,
                                       df.head(lexical_d_node) == lexical_d_node)
                                   for lexical_d_node in df.lex1nodes()])
                               for df_id, df in self.derivation_formulas.items()])
            return And(constraint_A, constraint_B, constraint_C)

        return PbLe([(get_term(entry), 1) for entry in lf.entries], k=k)


    def minimize_num_features(self, k):
        # Minimize the total number of syntactic features.
        lf = self.lexicon_formula
        def get_term(entry, l_node):
            return And(lf.lnodeType(l_node) != lf.LTypeSort.Inactive,
                       Or([lf.pf_map(entry.nodes[0], pf_node)
                           for pf_node in lf.pfInterface.non_null_nodes()]))

        return PbLe([(get_term(entry, l_node), 1)
                     for entry in lf.entries
                     for l_node in entry.nodes],
                     k=k)


    def minimize_num_derivation_nodes(self, k):
        lf = self.lexicon_formula
        return PbLe([(df.head(x) != df.null_node, 1)
                     for df in self.derivation_formulas.values()
                     for x in df.nodes()],
                    k=k)


    def maximize_num_used_selectional_features(self, k):
        # Maximize the number of distinct selectional features that are used.
        lf = self.lexicon_formula
        return PbGe([(Or([And(lf.featLbl(x) == sel_feat,
                              lf.lnodeType(x) != lf.LTypeSort.Inactive)
                          for entry in lf.entries
                          for x in entry.nodes]),
                      1)
                     for sel_feat in lf.selectional_syn_feats],
                    k=k)


    def minimize_num_used_selectional_features(self, k):
        # Minimize the number of distinct selectional features that are used.
        lf = self.lexicon_formula
        return PbLe([(Or([And(lf.featLbl(x) == sel_feat,
                              lf.lnodeType(x) != lf.LTypeSort.Inactive)
                          for entry in lf.entries
                          for x in entry.nodes]),
                      1)
                     for sel_feat in lf.selectional_syn_feats],
                    k=k)
