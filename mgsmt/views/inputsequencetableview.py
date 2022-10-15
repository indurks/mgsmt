#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
LaTeX tabular display of the input sequence.
"""

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2019-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from z3 import *
import mgsmt
from IPython.display import display, Math, Image
import contextlib, os, shutil, subprocess, time, uuid

from mgsmt.views.view_utils import display_latex


LATEX_TEMPLATE = r"""
\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage{adjustbox}
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{booktabs}
\usepackage{graphicx}
\usepackage{lscape}
\usepackage{multirow}
\usepackage[table]{xcolor}
\definecolor{lightgray}{gray}{0.9}

\begin{document}
\pagenumbering{gobble}
\begin{figure}[!ht]
\centering
\noindent\adjustbox{width=\textwidth,max width=\textwidth}{

\rowcolors{1}{}{lightgray}
\begin{tabular}{ll%s}
\toprule
$I_{i}$ & (Tokenized) Sentence & Locality Constraints \\
\midrule
%s
\bottomrule
\end{tabular}
}
{\small
\caption{Model Input — A Sequence of Sentences Annotated with Syntactic
Relations. Some phonetic forms have their category pre-specified, indicated by
a suffix of a slash followed by the category. Locality constraints include
agreement ($Agr$) and predicate-argument structure (i.e. a $\theta$ grid), with
the predicate indicated in the suffix and the subject, object and indirect
object components marked by ``s:'', ``o:'' and ``i:'' respectively. The type 
of the sentence -- i.e. either declarative or interrogative -- is also annotated 
on each sentence, indicated by the end-of-sentence punctuation.}
}
\end{figure}
\end{document}
"""


class InputSequenceTableView:

    def __init__(self,
                 ics,
                 display_categories=True,
                 display_index=True,
                 display_categories_in_superscript=False,
                 locality_column_width=r"p{0.5\textwidth}",
                 locality_column_wraparound=True):
        self.ics = ics
        self.display_categories = display_categories
        self.display_index = display_index
        self.display_categories_in_superscript = display_categories_in_superscript
        self.locality_column_width = locality_column_width
        self.locality_column_wraparound = locality_column_wraparound


    def export(self, serialize_tex=True, compile_pdf=True):
        pass


    def display(self, dir_name, file_name):
        self.latex_source_filepath = dir_name + '/' + file_name + '.tex'
        return display_latex(self.get_latex_source(),
                             dir_name,
                             file_name,
                             visualize=False,
                             include_rotation=False)


    def get_latex_source(self):
        def prep_token(w, idx=None, pos=None):
            if not(self.display_categories):
                pos = None
            if not(self.display_index):
                idx = None
            cat_str = "^" if self.display_categories_in_superscript else "/"
            if pos is not None:
                pos = pos.replace('C_declarative', r'C\_{declarative}')
                pos = pos.replace('C_question', r'C\_question')
            if idx is None and pos is None:
                return r"\text{%s}"%(w)
            elif idx is None:
                return r"\text{%s}%s{\text{%s}}"%(w, cat_str, pos)
            elif pos is None:
                return r"\text{%s}_{%d}"%(w, idx)
            else:
                return r"\text{%s}_{%d}%s{\text{%s}}"%(w, idx, cat_str, pos)

        def prep_sent(ic):
            def get_pos(x, word):
                ccs = ic.constraints['structural']['categorical']
                for pos, entries in ccs.items():
                    if (word, x) in entries:
                        return pos
                return None
            sent = "\ ".join([prep_token(w, idx=i, pos=get_pos(i, w))
                              for i, w in enumerate(ic.constraints['surface'])])
            if ic.constraints['structural']['sent_type'] == 'declarative':
                sent += " ."
            elif ic.constraints['structural']['sent_type'] == 'question':
                sent += " ?"
            return sent

        def prep_phrase(lc_value, m):
            if m not in lc_value:
                return ""
            return m[0] + "\colon" + "\ ".join(prep_token(w=w, idx=idx) for w, idx in lc_value[m])
                                               

        def prep_struct_constraints(ic):
            result = []

            for lc_type, lc_value in ic.constraints['structural']['locality']:
                pred_token = prep_token(w=lc_value['pred'][0][0], idx=lc_value['pred'][0][1])
                if lc_type == "theta":
                    arg_token = ", ".join(prep_phrase(lc_value, m)
                                          for m in ('subj', 'obj', 'iobj')
                                          if prep_phrase(lc_value, m) != "")
                    result.append(r"\theta_{%s}[%s]"%(pred_token, arg_token))
                elif lc_type == "agree":
                    arg_token = prep_phrase(lc_value, m='subj')
                    result.append(r"{Agr}_{%s}[%s]"%(pred_token, arg_token))

            if self.locality_column_wraparound:
                return ", ".join([f"${x}$" for x in result])
            else:
                return "$%s$"%(", ".join(result))

        table_str = ""
        for i, ic in enumerate(self.ics):
            row = ["$I_{%d}$"%(i), "$%s$"%(prep_sent(ic)), prep_struct_constraints(ic)]
            table_str += " & ".join(row) + r" \\" + "\n"

        return LATEX_TEMPLATE%(self.locality_column_width,
                               table_str)
