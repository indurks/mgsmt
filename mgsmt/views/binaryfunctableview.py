#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from z3 import *

import mgsmt
from mgsmt.views.view_utils import display_latex

from IPython.display import display, Math, Image
import contextlib, os, shutil, subprocess, time, uuid

LATEX_DOC_TEMPLATE = r"""
\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage{adjustbox}
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{bm}
\usepackage{booktabs}
\usepackage{graphicx}
\usepackage{lscape}
\usepackage[table]{xcolor}
\definecolor{lightgray}{gray}{0.9}

\newcommand{\bftcplus}{\pmb{\scalebox{1.5}{$\oplus$}}}
\newcommand{\bftplus}{\pmb{\scalebox{1.5}{$+$}}}
\newcommand{\bftcirc}{\pmb{\scalebox{1.2}{$\bigcirc$}}}
\newcommand{\bftdot}{$\cdot$}

\begin{document}
\pagenumbering{gobble}

\begin{landscape}
\begin{table}[h!]
\centering
{\small
\resizebox{\columnwidth}{!}{
\begin{tabular}{%s}
\toprule
%s \\
\midrule
%s
\bottomrule
\end{tabular}
}
\caption{Model Interpretation of the binary uninterpreted functions %s.}
}
\end{table}
\end{landscape}
\end{document}
"""


class BinaryFuncTableView():

    def __init__(self, derivation_model):
        self.binary_pred_name = "???"
        df = derivation_model.formula
        self.nodes = list(df.all_nodes())
        z3eval = derivation_model.model.evaluate

        def color(x, y):
            #return r"\cellcolor{%s}"%('blue' if z3eval(pred(x, y)) else 'red')
            dom_is_true = str(z3eval(df.dominates(x, y))) == "True"
            nmdom_is_true = str(z3eval(df.nmdom(x, y))) == "True"
            sym_table = {(True, True): r"\bftcplus",
                         (True, False): r"\bftcirc",
                         (False, True): r"\bftplus",
                         (False, False): r"\bftdot"}
            #print(sym_table.keys())
            #print(sym_table[(False, False)])
            #print(str(dom_is_true))
            return sym_table[(dom_is_true, nmdom_is_true)]
            #return 'X' if z3eval(pred(x, y)) else '.'

        sorted_nodes = list(sorted(self.nodes, key= lambda k: self.get_id_from_node(k)))
        self.headers = ['~'] + [(r"\rotatebox{90}{" + self.node_id(c_node) + r"}")
                                for c_node in sorted_nodes]
        self.rows = [[self.node_id(r)] + [color(r, c) for c in sorted_nodes]
                     for r in sorted_nodes]

    def get_id_from_node(self, node):
        return int(str(node).split('_')[-1])

    def node_id(self, node):
        n_id = self.get_id_from_node(node)
        assert 0 <= n_id
        return "$D_{%d}$"%n_id

    def latex_src(self, verbose=True):
        col_str = "l|" + "".join(r'@{\hskip 0.5mm}c' for _ in range(len(self.headers)-1))
        col_name_str = " & ".join(self.headers)
        row_strs = [" & ".join(row) + " \\\\ \n" for row in self.rows]
        table_str = " ".join(row_strs)
        doc_str = LATEX_DOC_TEMPLATE%(col_str, col_name_str, table_str, self.binary_pred_name)
        if verbose:
            print(doc_str)
        return doc_str
