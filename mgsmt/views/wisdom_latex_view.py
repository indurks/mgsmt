#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2019-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

#from z3 import *

import mgsmt
import mgsmt.views.view_utils as view_utils

from IPython.display import display, Math, Image
import contextlib, copy, itertools, os, shutil, subprocess, time, uuid

LATEX_TEMPLATE = r"""\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage{adjustbox}
\usepackage{amsmath}
\usepackage{booktabs}
\usepackage{graphicx}
\usepackage{multirow}
\usepackage{lscape}
\usepackage[table]{xcolor}
\definecolor{lightgray}{gray}{0.9}

\begin{document}
\pagenumbering{gobble}
\begin{table}[h!]
\centering
\rowcolors{1}{}{lightgray}
\begin{tabular}{%s}
\toprule
%s \\
\midrule
%s
\bottomrule
\end{tabular}
\caption{%s}
\end{table}
\end{document}
"""

class WisdomLaTeXView:

    def __init__(self, wisdom_history):
        self.wisdom_history = wisdom_history


    def display(self, dir_name, file_name):
        self.latex_source_filepath = dir_name + '/' + file_name + '.tex'
        return view_utils.display_latex(self.get_latex_source(),
                                        dir_name,
                                        file_name,
                                        visualize=False,
                                        include_rotation=False)


    def pp_constraints_as_tabular_env(self, constraints):
        results = [f"$(%s)\\times(%s)$"%(constraint['intruder']['str_repr'],
                                         constraint['proj_child']['str_repr'])
                   for constraint in constraints]
        results = [x.strip().replace('ε', '\epsilon').replace('·', '\\cdot')
                   for x in results]
        if not(results):
            return '~'
        else:
            return "\\begin{tabular}{c}" + ' \\\\ '.join(results) + "\\end{tabular}"


    def get_latex_source(self):
        num_rows = len(self.wisdom_history)
        assert len(set([len(w) for w in self.wisdom_history])) == 1
        num_levels = len(self.wisdom_history[0])

        header_row = ["Iteration"]
        for i, level in enumerate(self.wisdom_history[-1]):
            assert i == level['level']
            header_row += ["${MV}_{%d}$"%(i), "$C_{%d}$"%(i)]
        header_str = " & ".join(header_row)

        def clean_entry(x):
            if x == 0:
                return "-"
            return x if type(x) == str else str(x)

        body_rows = []
        for i, wisdom in enumerate(self.wisdom_history):
            body_row = [str(i+1)]
            body_row += itertools.chain(*[[level['min_value'],
                                           len(level['constraints'])]
                                          for level in wisdom])
            body_rows.append([clean_entry(x) for x in body_row])
        body_str = "\n".join(r" & ".join(row) + r" \\" for row in body_rows)
        caption_str = "Wisdom History for Inference Experiment."
        return LATEX_TEMPLATE%("c"*len(header_row),
                               header_str,
                               body_str,
                               caption_str)
