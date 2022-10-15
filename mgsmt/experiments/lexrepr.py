#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2019-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import itertools, json, pprint as pp
from itertools import product

from z3 import And, Or, Not, Implies, Xor, Distinct, If, PbEq, PbGe, PbLe
from z3 import BoolSort

import mgsmt.formulas.lexiconformula
import mgsmt.formulas.derivationformula
from mgsmt.solver.solver_utils import distinct


class LRLexEntry:

    def __init__(self, pf, sfs, cat):
        self.pf = pf
        self.sfs = sfs
        self.cat = cat

    def sfs_str(self):
        return ','.join(['%s%s'%(x, y) for (x, y) in self.sfs])

    def __str__(self):
        return f"{self.pf}::{self.sfs_str()}"

    def __repr__(self):
        return repr((self.pf, self.sfs, self.cat))


class LexRepr:

    def __init__(self,
                 json_strs=None,
                 lexicon_model=None,
                 derivation_models=(),
                 lex_items=None,
                 **opts):
        if json_strs is not None:
            def proc_sf(sf):
                if 'normalize_features' in opts:
                    return (sf[0], opts['normalize_features'].get(sf[1], sf[1]))
                return tuple(sf)
            entries = set([(entry['pf'],
                            tuple(map(proc_sf, entry['sfs'])),
                            entry.get('cat', ''))
                           for x in json_strs
                           for entry in json.loads(x)])
            self.lex_entries = [LRLexEntry(*e) for e in entries]
        elif lex_items is not None:
            lex_items = json.loads(lex_items)
            entries = set([(entry['pf'],
                            tuple([tuple(sf) for sf in entry['sfs']]),
                            entry['cat'])
                           for entry in lex_items])
            self.lex_entries = [LRLexEntry(*entry) for entry in entries]
        elif lexicon_model is not None:
            lm = self.lexicon_model = lexicon_model
            lf = lm.formula
            m_eval = lm.model.evaluate

            def include_node(l_node, pf_node):
                if not derivation_models:
                    return True
                # At least one of the lexical nodes in one of the derivations
                # must connect to l_node.
                term = Or([And(lf.derivations[dm.formula.formula_name]['bus'](d_node) == l_node,
                               dm.formula.pf_map(d_node) == pf_node)
                           for dm in derivation_models
                           for d_node in dm.formula.lex1nodes()])
                result = m_eval(term)
                return result

            self.lex_entries = [LRLexEntry(pf=lf.pfInterface.get_pf(pf_node),
                                           sfs=[lm.pp_term(x) for x in le['features']],
                                           cat=str(lm.model.evaluate(lm.formula.cat_map(s_node))))
                                for s_node, le in lexicon_model.lexical_entries.items()
                                for pf_node in lf.pfInterface.non_null_nodes()
                                if m_eval(lf.pf_map(s_node, pf_node)) and include_node(s_node, pf_node)]


    def _mapping_to_formula(self, lexicon_formula):
        mapping = []
        used_lf_le = []
        missing_lr_le = []
        for lr_le in self.lex_entries:
            for lf_le in lexicon_formula.entries:
                if lf_le in used_lf_le:
                    continue
                assert type(lr_le.pf) == type(lf_le.word), (type(lr_le.pf), type(lf_le.word))
                if lr_le.pf == lf_le.word:
                    mapping.append((lr_le, lf_le))
                    used_lf_le.append(lf_le)
                    break
            else:
                missing_lr_le.append(lr_le)
        unused_lf_le = [x for x in lexicon_formula.entries if x not in used_lf_le]
        return mapping, unused_lf_le


    def _impose_constraints_syn_feats(lexicon_formula, lr_sf, lf_sf_node, constrain_sf_labels=True):
        terms = []
        lf = lexicon_formula
        f_type_str, f_val_str = lr_sf
        f_type = lf.strToLType(f_type_str)
        head_movement = f_type_str[0] in ('<', '>')
        assert f_type is not None, (f"Could not find: {f_type_str}", type(f_type_str))
        if not(f_type == lf.LTypeSort.Complete):
            terms.append(lf.lnodeType(lf_sf_node) == f_type)
            terms.append(lf.head_movement(lf_sf_node) == head_movement)
            for v in lf.syn_feats:
                if f_val_str == lf.get_feature_str(v):
                    if constrain_sf_labels:
                        terms.append(lf.featLbl(lf_sf_node) == v)
                    break
            else:
                raise Exception("Could not find the feature value: %r"%(f_val_str))
        return terms


    def _impose_constraints_on_succ_func(lexicon_formula, lr_le, lf_le):
        terms = []
        # Constraints for the LF's successor function.
        lf = lexicon_formula
        f_type_str, _ = lr_le.sfs[-1]
        ends_complete = lf.strToLType(f_type_str) == lf.LTypeSort.Complete
        num_nodes = len(lr_le.sfs) - (1 if ends_complete else 0)
        terms.extend([lf.succ(lf_le.nodes[i]) == lf_le.nodes[i+1] for i in range(num_nodes-1)])
        if ends_complete:
            terms.append(lf.succ(lf_le.nodes[num_nodes-1]) == lf.complete_node)
            #terms.append(lf.succ(lf_le.nodes[-2]) == lf.complete_node)
        else:
            terms.append(lf.succ(lf_le.nodes[num_nodes-1]) == lf.terminal_node)
            #terms.append(lf.succ(lf_le.nodes[-1]) == lf.terminal_node)
        return terms


    def _impose_constraints_lexical_entry(lexicon_formula, lr_le, lf_le, constrain_sf_labels=True):
        assert type(lr_le) is LRLexEntry, (lr_le, type(lr_le))
        assert type(lf_le) is mgsmt.formulas.lexiconformula.LexicalEntry, (lf_le, type(lf_le))
        lf, cs = lexicon_formula, mgsmt.formulas.derivationformula.DerivationFormula.CatSort
        str2cat = { 'C_declarative': cs.C_declarative, 'C_question': cs.C_question,
                   'T': cs.T, 'v': cs.v, 'V': cs.V, 'P': cs.P, 'D': cs.D, 'N': cs.N}
        terms = []
        # Constraints for features that are used.
        for i, lr_sf in enumerate(lr_le.sfs):
            terms.extend(LexRepr._impose_constraints_syn_feats(lexicon_formula,
                                                               lr_sf,
                                                               lf_le.nodes[i],
                                                               constrain_sf_labels))
        # Constraints for features that are not used.
        terms.extend([And(lf.lnodeType(x) == lf.LTypeSort.Inactive, lf.featLbl(x) == lf.nil_syn_feature)
                      for x in lf_le.nodes[len(lr_le.sfs):]])
        # Constraints for the successor function.
        terms.extend(LexRepr._impose_constraints_on_succ_func(lexicon_formula, lr_le, lf_le))
        # Constraints for the categories.
        terms.append(lf.cat_map(lf_le.nodes[0]) == str2cat[lr_le.cat])
        return terms


    def impose_constraints_lexicon(self, lexicon_formula, verbose=False):
        s = lexicon_formula.solver
        lf = lexicon_formula
        mapping, unused_lf_le = self._mapping_to_formula(lf)
        if verbose:
            print("mapping:")
            pp.pprint([(k, str(v)) for k, v in mapping])
        with s.group(tag=f"Ruling out unused lexical entries."):
            s.add_conj([lf.lnodeType(le.nodes[0]) == lf.LTypeSort.Inactive
                        for le in unused_lf_le])
        for lr_le, lf_le in mapping:
            if verbose:
                print(f"processing: {str(lr_le)}")
            terms = LexRepr._impose_constraints_lexical_entry(lexicon_formula, lr_le, lf_le)
            try:
                with s.group(tag=f"Imposing Constraints for a Lexical Entry: {str(lr_le)}"):
                    s.add_conj(terms)
            except:
                pp.pprint(terms)


    def _get_data_repr(self, derivation_model=None):
        relevant_lex_entries = []

        data_repr = [{'pf': le.pf, 'sfs': le.sfs, 'cat': le.cat}
                     for le in self.lex_entries]
        return list(sorted(data_repr, key=lambda k: repr(k)))


    def json(self, filepath=None, derivation_model=None):
        if filepath:
            with open(filepath, 'w') as f_json:
                json.dump(self._get_data_repr(derivation_model=derivation_model), f_json, sort_keys=True)
        else:
            return json.dumps(self._get_data_repr(derivation_model=derivation_model), sort_keys=True)


    def __repr__(self):
        return str(self._get_data_repr())


    def __str__(self, separator='\n'):
        return separator.join(str(le) for le in sorted(self.lex_entries, key=lambda k: k.pf))


    def enum_pforms(self):
        return list(sorted([le.pf for le in self.lex_entries]))


    def latex(self):
        for le in sorted(self.lex_entries, key=lambda x: (x.pf, x.cat, x.sfs)):
            pf_str = le.pf.replace('ε', r'\epsilon') if 'ε' in le.pf else r"\text{%s}"%(le.pf)
            sfs_str = le.sfs_str().replace('~', '{\sim}')
            yield r"$%s{\ ::}%s$"%(pf_str, sfs_str)
