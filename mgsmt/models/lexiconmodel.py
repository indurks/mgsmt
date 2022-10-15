#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
An SMT-model of a minimalist lexicon.
"""

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import json
from typing import List
from z3 import And, Or, Not, Implies, Xor, Distinct, If, PbEq, PbGe, PbLe

import mgsmt.formulas.lexiconformula

class LexiconModel:

    def __init__(self, lexicon_formula, model):
        assert isinstance(lexicon_formula,
                          mgsmt.formulas.lexiconformula.LexiconFormula)
        self.formula = lexicon_formula
        self.model = model

        # From each start node trace out the successor nodes until reaching the
        # Terminal node.
        def walk_nodes(node):
            while self.model.evaluate(node != self.formula.terminal_node):
                yield node
                node = self.model.evaluate(self.formula.succ(node))

        active_start_nodes = set()
        for df_name, entry in lexicon_formula.derivations.items():
            for d_node in entry['formula'].lex1nodes():
                for l_node in lexicon_formula.enum_usable_nodes(is_start_node=True):
                    bus = entry['bus']
                    head = entry['formula'].head
                    null_node = entry['formula'].null_node
                    if self.model.evaluate(And(head(d_node) != null_node,
                                               bus(d_node) == l_node)):
                        active_start_nodes.add(l_node)

        self.lexical_entries = {}
        crossings = self.get_pf_lexicon_crossing_occurrences()
        for s_node in active_start_nodes:
            cat = self.model.evaluate(self.formula.cat_map(s_node))
            pfs = [self.formula.pfInterface.get_pf(pf_nd)
                   for pf_nd in self.formula.pfInterface.non_null_nodes()
                   if self.model.evaluate(self.formula.pf_map(s_node, pf_nd) == True)]
            self.lexical_entries[s_node] = {
                'features': tuple(walk_nodes(s_node)),
                'pfs': tuple(pfs),
                'cat': cat
            }


    def get_pf_lexicon_crossing_occurrences(self):
        # Compute the stripped down (factored) lexicon.
        crossings = {}
        m_eval = self.model.evaluate
        lf = self.formula
        ds = lf.derivations
        for pf_node in lf.pfInterface.non_null_nodes():
            for lex_entry in lf.entries:
                l_node = lex_entry.nodes[0]
                occurred = m_eval(Or([And(df_entry['bus'](d_node) == l_node,
                                          df_entry['formula'].head(d_node) != df_entry['formula'].null_node,
                                          lf.lnodeType(l_node) != lf.LTypeSort.Inactive,
                                          df_entry['formula'].pf_map(d_node) == pf_node,
                                          lf.pf_map(l_node, pf_node))
                                      for df_id, df_entry in ds.items()
                                      for d_node in df_entry['formula'].lex1nodes()]))
                crossings[(pf_node, l_node)] = occurred
                for x in lex_entry.nodes[1:]:
                    crossings[(pf_node, x)] = False
        return crossings


    def str(self, abridged=True):
        s = str(self.model)
        if abridged:
            s = s.replace('_feature_label', '_feat_lbl')
            s = s.replace('_LexiconNode_', '_LexNd_')
            s = s.replace('_successor', '_succ')
            s = s.replace('_LexiconFeatureLabel_', '_LexFeatNd_')
        return s

    def repr(self):
        return self.str(abridged=True)

    def pp_term(self, term, LaTeX=False, HTML=False):
        f, m = self.formula, self.model

        # We may want to make the feature label pretty.
        term_feat_lbl = f.get_feature_str(m.evaluate(f.featLbl(term)))
        if len(term_feat_lbl) >= 2 and term_feat_lbl[0].isalpha() and (term_feat_lbl[1:]).isdigit():
            if LaTeX:
                term_feat_lbl = "{%s}_{%s}"%(term_feat_lbl[0], term_feat_lbl[1:])
            elif HTML:
                HTML_str = r'%s<SUB><FONT POINT-SIZE="10">%s</FONT></SUB>'
                term_feat_lbl = HTML_str%(term_feat_lbl[0], term_feat_lbl[1:])

        f_pair = f.ltypeToStr(term_type=m.evaluate(f.lnodeType(term)),
                             term_feat_lbl=term_feat_lbl,
                             head_movement=m.evaluate(f.head_movement(term)))
        if HTML:
            return (f_pair[0].replace("<=", r"&#60;="), f_pair[1])
        else:
            return f_pair

    def get_indexed_lexical_entry(self, l_node):
        f, m = self.formula, self.model
        if m.evaluate(Distinct(f.complete_node, f.terminal_node, l_node)):
            for s_node, entry in self.lexical_entries.items():
                for i, x in enumerate(entry['features']):
                    if self.model.evaluate(l_node == x):
                        return (i, entry)

    def get_lexical_entry_components(self, lexical_entry, LaTeX=False, HTML=False):
        cat_str = str(lexical_entry['cat'])
        if HTML:
            if cat_str == 'C_declarative':
                cat_str = 'C<SUB>declarative</SUB>'
            elif cat_str == 'C_question':
                cat_str = 'C<SUB>question</SUB>'

        feat_str = ["%s%s"%(self.pp_term(f, LaTeX=LaTeX, HTML=HTML))
                    for f in lexical_entry['features']]

        return (lexical_entry['pfs'], feat_str, cat_str)


    def pp_lexical_entry(self, lexical_entry, feat_idx=0):
        pf_strs, feats, cat_str = self.get_lexical_entry_components(lexical_entry)
        if feat_idx == 0:
            feat_str = ','.join(feats)
        else:
            feat_str = "%s·%s"%(','.join(feats[:feat_idx]),
                                ','.join(feats[feat_idx:]))
        separator_str = '::' if feat_idx == 0 else ':'
        return f"{pf_strs}/{cat_str}{separator_str}{feat_str}"

    def pp_str_repr(self, display_index=True):
        entries = sorted(self.lexical_entries.values(),
                         key=lambda x: (x['pfs'], len(x['features'])))
        lines = ["%s%s"%("%d. "%(i+1) if display_index else "",
                         self.pp_lexical_entry(entry))
                 for i, entry in enumerate(entries)]
        return lines

    def pretty_print(self, display_index=True):
        for line in self.pp_str_repr(display_index=display_index):
            print(line)

    def json_repr(self):
        return '[%s]'%(', '.join('"%s"'%(x) for x in self.pp_str_repr(display_index=False)))

    def latex(self):
        crossings = self.get_pf_lexicon_crossing_occurrences()
        for le in sorted(self.lexical_entries.values(),
                         key=lambda x: (x['pfs'], len(x['features']))):
            raw_pf_strs, feats, cat_str = self.get_lexical_entry_components(le, LaTeX=True)
            pf_strs = []
            for pf_str in raw_pf_strs:
                p_node = self.formula.pfInterface.get_pf_node(pf_str)
                l_node = le['features'][0]
                if crossings[(p_node, l_node)]:
                    pf_strs.append(pf_str)
            # Only allow members of pf_strs that are valid connections.
            # The following substitutions are required by LaTeX.
            pf_strs = [pf_str.replace('ε', r'\epsilon') if 'ε' in pf_str else r"\text{%s}"%pf_str
                       for pf_str in pf_strs]
            cat_str = cat_str.replace("C_declarative", "C_{declarative}")
            cat_str = cat_str.replace("C_question", "C_{question}")
            feat_str = ','.join([f.replace('~', r'{\sim}') for f in feats])
            joint_pf_strs = ','.join(pf_strs)
            joint_pf_strs = r"\{%s\}"%(joint_pf_strs) if len(pf_strs) > 1 else joint_pf_strs
            yield r"${%s}/%s{\ ::}%s$"%(joint_pf_strs, cat_str, feat_str)
