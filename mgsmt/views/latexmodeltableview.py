#!/usr/bin/env python3
# -*- coding: utf-8 -*-


__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from z3 import *
import mgsmt
from mgsmt.views.modeltableview import ModelTableView
from mgsmt.views.view_utils import display_latex

from IPython.display import display, Math, Image
import contextlib, os, shutil, subprocess, time, uuid


class LexiconModelTableView(ModelTableView):

    def __init__(self, derivation_model, lexicon_model=None):
        super()
        self.dm = derivation_model
        self.nodes = list(self.dm.formula.all_nodes())
        z3eval = self.dm.model.evaluate
        df = self.dm.formula

        def str_replace_reduce(s, replacements):
            if s is None:
                return ""
            for x, y in replacements:
                s = s.replace(x, y)
            return s

        def node_type_str(node):
            mapping = [
                ([df.null_node], 'Bottom'),
                (list(df.overt2lex2nodes()), 'Leaf'),
                (list(df.covert3lex3nodes()), 'Leaf'),
                (list(df.intermediate4nodes()), 'Non-Leaf'),
                ([df.root_node], 'Non-Leaf (Root)')
            ]
            for ns, t_str in mapping:
                for n in ns:
                    if z3eval(n == node):
                        return t_str
            else:
                raise Exception("%r not in %r"%(node, df.formula_name))

        def node_id(node):
            node_id = int(str(node).split('_')[-1])
            assert 0 <= node_id
            return "$D_{%d}$"%(node_id)

        def lex_node(d_node):
            if lexicon_model is None:
                return None
            bus = lexicon_model.formula.derivations[df.formula_name]['bus']
            return z3eval(bus(d_node))

        def lex_entry_str(d_node):
            replacements = [('∅', '\emptyset'),
                            ('·', ' \cdot '),
                            ('ε', r'\epsilon'),
                            ("C_declarative", "C_{decl.}"),
                            ("C_question", "C_{ques.}"),
                            ('~', r'{\sim}')]
            le_str = self.dm.get_lex_entry_str(d_node, lexicon_model)
            le_str = str_replace_reduce(le_str, replacements)
            return "$%s$"%(le_str)

        def cat_str(d_node):
            c_str = str(z3eval(df.cat_map(d_node)))
            replacements = [("null", ""),
                            ("C_declarative", "$C_{decl.}$"),
                            ("C_question", "$C_{ques.}$")]
            return str_replace_reduce(c_str, replacements)

        def pform_str(d_node):
            pf_str = df.pfInterface.get_pf(z3eval(df.pf_map(d_node))) 
            replacements = [('∅', ''), ('ε', '$\epsilon$')]
            return str_replace_reduce(pf_str, replacements)

        self.column_scheme = [
            ('Node ID', node_id),
            ('Node Type', node_type_str),
            ('PForm', pform_str),
            ('Cat.', cat_str),
            ('Head',   lambda x: node_id(z3eval(df.head(x)))),
            ('Parent', lambda x: node_id(z3eval(df.parent(x)))),
            ('$M_{P}$', lambda x: node_id(z3eval(df.move_loc(x)))),
            ('$M_{H}$', lambda x: node_id(z3eval(df.head_movement(x)))),
            ('Assoc. Lex. Entry', lex_entry_str),
            #('Lexicon Node', lambda x: lex_node(x)),
        ]

        self.headers = [header for (header, _) in self.column_scheme]
        handle_empty_entry = lambda e: e if e else "~"
        self.rows = [[handle_empty_entry(fn(node))
                      for (_, fn) in self.column_scheme]
                     for node in self.nodes]

    def print_table(self):
        raise NotImplementedError
        title = "Derivation Model %s"%(self.dm.formula.formula_name)
        super().display_table(rows=self.rows, headers=self.headers, title=title)

    def latex_src(self, sent_idx, num_sents, sent, verbose=True):
        col_str = "".join('l' for _ in self.headers)
        col_name_str = " & ".join(self.headers)
        row_strs = [" & ".join(row) + " \\\\ \n" for row in self.rows]
        table_str = " ".join(row_strs)
        caption_str = LATEX_CAPTION_TEMPLATE%(sent_idx, num_sents, sent)
        doc_str = LATEX_DOC_TEMPLATE%(col_str, col_name_str, table_str, caption_str)
        if verbose:
            print(doc_str)
        return doc_str
