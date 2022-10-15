#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Tabular display of a Lexicon Model.
"""

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

LATEX_DOC_TEMPLATE = r"""
\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage{adjustbox}
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{booktabs}
\usepackage{graphicx}
\usepackage{lscape}
\usepackage[table]{xcolor}
\definecolor{lightgray}{gray}{0.9}
\begin{document}
\pagenumbering{gobble}
\begin{landscape}
\begin{table}[h!]
\centering
{\small
\rowcolors{1}{}{lightgray}
\begin{tabular}{%s}
\toprule
%s \\
\midrule
%s
\bottomrule
\end{tabular}
\caption{Model Interpretation of the inferred lexicon. Values are supplied for 
the uninterpreted functions that are used in the formulas that encode the lexicon. 
The lexicon nodes that encode the syntactic features in a lexical entry are 
sequenced by the successor function. Lexicon nodes not listed here are 
\emph{inactive} and do not encode any lexical entry in the lexicon.}
\end{table}
\end{landscape}
\end{document}
"""


class LexiconModelTableView(ModelTableView):

    def __init__(self, lexicon_model):
        self.lm = lexicon_model
        self.nodes = self.lm.formula.nodes
        z3eval = self.lm.model.evaluate
        lf = self.lm.formula
        crossings = self.lm.get_pf_lexicon_crossing_occurrences()

        def str_replace_reduce(s, replacements):
            if s is None:
                return ""
            for x, y in replacements:
                s = s.replace(x, y)
            return s
        
        def node_id(node):
            s = str(node)
            node_id = int(s.split('_')[-1])
            assert 0 <= node_id
            return "$L_{%d}$"%(node_id)

        def get_lexical_entry(l_node):
            result = lexicon_model.get_indexed_lexical_entry(l_node)
            if result == None:
                return None
            i, entry = result
            return lexicon_model.pretty_print_entry(entry, feat_idx=i)

        def pform(l_node):
            raw_pf_strs = [lf.pfInterface.get_pf(pf_node)
                           for pf_node in lf.pfInterface.non_null_nodes()
                           if z3eval(lf.pf_map(l_node, pf_node))]

            pf_strs = []
            for pf_str in raw_pf_strs:
                p_node = lf.pfInterface.get_pf_node(pf_str)
                if crossings[(p_node, l_node)]:
                    pf_strs.append(pf_str)
            pf_str = ','.join(pf_strs)

            return str_replace_reduce(pf_str, [('∅', ''), ('ε', '$\epsilon$')])
        
        def feat_type(l_node):
            t = lexicon_model.pp_term(l_node)
            if not t:
                return ""
            f_str = str(t[0])
            replacements = dict([('<=', r'Selector ($<=$)'),
                                 ('>=', r'Selector ($>=$)'),
                                 ('=', r'Selector ($=$)'),
                                 ('~', r'Selectee (${\sim}$)'),
                                 ('+', r'Licensor ($+$)'),
                                 ('-', r'Licensee ($-$)'),
                                 ('C', r'$C$')])
            assert f_str in replacements, f_str
            return replacements[f_str]

        def feat_value(l_node):
            t = lexicon_model.pp_term(l_node, LaTeX=True)
            return "" if not t else f"${t[1]}$"

        self.column_scheme = [
            ('Node ID', node_id),
            ('Phon. Form', pform),
            ('Succ.', lambda x: node_id(z3eval(lf.succ(x)))),
            ('Feat. Type', feat_type),
            ('Feat. Value', feat_value)
        ]

        self.headers = [header for (header, _) in self.column_scheme]
        self.rows = [[fn(node) for (_, fn) in self.column_scheme]
                     for node in self.nodes]


    def display(self, dir_name, file_name):
        self.latex_source_filepath = dir_name + '/' + file_name + '.tex'
        return display_latex(self.get_latex_source(),
                             dir_name,
                             file_name,
                             visualize=False,
                             include_rotation=True)


    def get_latex_source(self, ignore_inactive_rows=True, verbose=False):
        col_str = "".join('l' for _ in self.headers)
        col_name_str = " & ".join(self.headers)

        def use_row(row):
            print([node_id(x)
                   for x in (lf.null_node,
                             lf.complete_node,
                             lf.terminal_node)])
            print(row)
            if not(ignore_inactive_rows):
                return True
            if row[3] != "":
                return True
            if row[0] == node_id(lf.null_node):
                return True
            if row[0] == node_id(lf.complete_node):
                return Truep
            if row[0] == node_id(lf.terminal_node):
                return True
            else:
                print(row)
                return False
        
        use_row = lambda row: (row[3] != "") or not(ignore_inactive_rows)
        row_strs = [" & ".join(row) + " \\\\ \n"
                    for row in self.rows
                    if use_row(row)]
        table_str = " ".join(row_strs)
        doc_str = LATEX_DOC_TEMPLATE%(col_str, col_name_str, table_str)
        if verbose:
            print(doc_str)
        return doc_str
