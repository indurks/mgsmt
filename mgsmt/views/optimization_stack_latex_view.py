#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import mgsmt
import mgsmt.views
import mgsmt.views.view_utils

import ipywidgets as widgets
from ipywidgets import interact
from ipywidgets import Label, HBox, VBox
from IPython.core.display import display, HTML

LATEX_DOC_TEMPLATE = r"""
\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage{adjustbox}
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{booktabs}
\usepackage{graphicx}
\usepackage{lscape}
\usepackage{rotating}
\usepackage{multirow}
\usepackage[table]{xcolor}
\definecolor{lightgray}{gray}{0.9}
\begin{document}
\pagenumbering{gobble}

\begin{landscape}
\begin{table}[h!]
\centering
\rowcolors{1}{}{lightgray}
\begin{tabular}{rrrlll}
\toprule
\multirow{2}{*}{Level} & \multirow{2}{*}{Optimization} & \multirow{2}{*}{Min. Value} & \multicolumn{3}{c}{Blocking Constraints} \\
\cline{4-6}
  &   &   &  Proj. Struct. & Non-Proj. Struct. & Interloping Struct. \\
\midrule
%s \\
\bottomrule
\end{tabular}
\caption{Optimization Stack. Each level of the optimization stack is associated with: 
(i) an \emph{optimization constraint} that seeks to minimize the size of the model in 
some manner, which is listed along with the minimum value computed for that constraint; 
(ii) blocking constraints formed from observing (in an overgeneration) which two 
structures were suppose to merge together, but an interloping structure instead merged 
with the non-projecting structure.}
\end{table}
\end{landscape}
\end{document}
"""


class OptimizationStackLaTeXView:

    def __init__(self, wisdom):
        self.wisdom = wisdom


    def display(self, dir_name, file_name):
        self.latex_source_filepath = dir_name + '/' + file_name + '.tex'
        return mgsmt.views.view_utils.display_latex(self.get_latex_source(),
                                                    dir_name,
                                                    file_name,
                                                    visualize=False,
                                                    include_rotation=True)


    def pp_constraints_as_tabular_env(self, constraints, constraint_key):
        results = ["$%s$"%(constraint[constraint_key]['str_repr']) for constraint in constraints]
        results = [x.strip().replace('ε', '\epsilon').replace('·', '\\cdot') for x in results]
        if not(results):
            return '~'
        else:
            return "\\begin{tabular}{c}" + ' \\\\ '.join(results) + "\\end{tabular}"


    def get_latex_source(self, include_index=True):

        def clean_entry(x):
            if type(x) == str:
                return x
            else:
                return str(x)

        rows = []
        for entry in self.wisdom:
            row = [entry['level'],
                   entry['label'].replace('_', '-'),
                   entry['min_value']]
            row += [self.pp_constraints_as_tabular_env(entry['constraints'], constraint_key)
                    for constraint_key in ('proj_child', 'nproj_child', 'intruder')]
            rows.append([clean_entry(x) for x in row])

        rows_str = (r' \\ ').join([' & '.join(row) for row in rows])
        return LATEX_DOC_TEMPLATE%(rows_str)
