#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2019-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from z3 import *

import mgsmt
from mgsmt.views.view_utils import display_latex

from IPython.display import display, Math, Image
import contextlib, copy, os, shutil, subprocess, time, uuid


LATEX_TEMPLATE = r"""\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage{adjustbox}
\usepackage{amsmath}
\usepackage{booktabs}
\usepackage{graphicx}
\usepackage{multirow}
\usepackage[table]{xcolor}
\definecolor{lightgray}{gray}{0.9}

\begin{document}
\pagenumbering{gobble}
\begin{table}[h!]
\centering
{\small
\begin{tabular}{%s}
\toprule
\multirow{2}{*}{Iteration} & \multicolumn{%d}{c}{Inference Set} & & \multicolumn{%d}{c}{Holdout Set} \\
\cline{2-%d}\cline{%d-%d}
%s \\
\midrule
%s
\bottomrule
\end{tabular}
\caption{%s}
}
\end{table}
\end{document}
"""


class OvergenerationDetectionExperimentResultsLatexView:

    def __init__(self, results, experiment, holdout_set=None, selections=None):
        self.experiment = experiment
        self.results = results
        self.holdout_set = holdout_set
        if selections:
            assert len(selections) == len(results), (len(selections), len(results))
            assert all([s in r for (s, r) in zip(selections, results)])
        self.selections = selections


    def display(self, dir_name, file_name):
        self.latex_source_filepath = dir_name + '/' + file_name + '.tex'
        return display_latex(self.get_latex_source(),
                             dir_name,
                             file_name,
                             visualize=False,
                             include_rotation=False)


    def get_latex_source(self):
        # Rows correspond to iterations of the OG-Detection procedure; columns
        # correspond to sentences being evaluated by the OG-Detection
        # procedure.
        df_ids = list(sorted(set([df_id
                                  for entry in self.results
                                  for df_id in entry])))

        e = self.experiment
        ic2df = e.grammar.ic2df
        df2ic = {v:k for k, v in ic2df.items()}

        def get_ic(df_id):
            ic_label = df2ic[df_id]
            for i, ic in enumerate(e.interface_conditions):
                if ic_label == ic.label:
                    return "$I_{%d}$"%(i+1)
            else:
                return "$I_{?}$"

        num_inference = len(df_ids)
        num_holdouts = 3

        # Header for the "Iteration" column.
        header_row = ["~"]

        # Headers for the "Inference Set" column.
        header_row += [get_ic(df_id) for df_id in df_ids]

        # Space between Inference Set and Holdout Set.
        header_row += ["~"]
        
        # Headers for the "Holdout Set" column.
        header_row += [f"$H_{i}$" for i in range(num_holdouts)]

        header_str = " & ".join(header_row)

        def get_entry(idx_entry, df_id, entry):
            # Compute the df_id'th entry of the idx_entry'th row.
            if df_id not in entry:
                return "-"
            value = str(len(entry[df_id]))
            if self.selections:
                if df_id == self.selections[idx_entry]:
                    return r"\boxed{" + value + "}"
            return value

        rows = []
        for idx, entry in enumerate(self.results):
            row_color = r"\rowcolor{%s}"%("lightgray" if idx % 2 == 0 else "white")
            row = [f"{row_color} {idx+1}"]
            row += [get_entry(idx, x, entry) for x in df_ids]
            row += ["~"]
            row += [str(i) for i in range(num_holdouts)]
            rows.append(row)

        body_str = "\n".join(r" & ".join(row) + r" \\" for row in rows)

        caption_str = "Overgeneration Detection Experiment Results."

        result = LATEX_TEMPLATE%("c"*len(header_row),
                                 num_inference,
                                 num_holdouts,
                                 num_inference+1,
                                 num_inference+3,
                                 num_inference+num_holdouts+2,
                                 header_str,
                                 body_str,
                                 caption_str)
        return result
