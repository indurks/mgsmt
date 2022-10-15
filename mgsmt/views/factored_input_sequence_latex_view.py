#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2019-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import collections, importlib

from z3 import *

import mgsmt
import mgsmt.views
import mgsmt.views.latex_widget
import mgsmt.views.view_utils as view_utils

from seriate import seriate
from scipy.spatial.distance import pdist

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

\begin{figure}[h!]
\centering

\noindent\adjustbox{width=7.6in,max width=10in}{
\rowcolors{3}{}{lightgray}
\begin{tabular}{%s}
\toprule
\multirow{2}{*}{ID} & \multirow{2}{*}{Category} & \multirow{2}{*}{Features} & \multicolumn{%s}{c}{Input Sentence} \\
\cline{4-%s}
& & %s \\
\midrule
%s
\bottomrule
\end{tabular}
}
{\small
\caption{Model Output -- A \emph{Factored} View of the Input Sequence.
Each row indicates which annotated sentences in the input sequence utilize 
each entry in the lexicon. The rows and columns have been seriated
(using the hamming distance metric) so as to visually group together similar
rows and columns.}
}
\end{figure}
\end{landscape}
\end{document}
"""

class FactoredInputSequenceLaTeXView:

    def __init__(self, grammar, display_counts=True, cluster_input_sentences=True):
        self.grammar = grammar
        self.crossings = self.get_ic_lexical_entry_crossings()
        self.latex_source_filepath = None
        self.display_counts = display_counts
        self.cluster_input_sentences = cluster_input_sentences


    def get_ic_lexical_entry_crossings(self):
        crossings = collections.defaultdict(int)
        lm = self.grammar.lexicon_model
        m_eval = lm.model.evaluate
        lf = lm.formula
        for ic_label in self.grammar.ic2df:
            df_id = self.grammar.ic2df[ic_label]
            df_entry = lf.derivations[df_id]
            df = df_entry['formula']
            for lex_entry in lf.entries:
                l_node = lex_entry.nodes[0]
                for d_node in df.lex1nodes():
                    occurred = m_eval(And(df_entry['bus'](d_node) == l_node,
                                          df.head(d_node) != df.null_node,
                                          lf.lnodeType(l_node) != lf.LTypeSort.Inactive))
                    if occurred:
                        crossings[(ic_label, l_node)] += 1
                for x in lex_entry.nodes[1:]:
                    crossings[(ic_label, x)] = 0
        return crossings


    def display(self, dir_name, file_name):
        self.latex_source_filepath = dir_name + '/' + file_name + '.tex'
        return view_utils.display_latex(self.get_latex_source(),
                                        dir_name,
                                        file_name,
                                        dpi=1200,
                                        visualize=False,
                                        include_rotation=True)


    def get_latex_source(self, include_index=True):
        lm = self.grammar.lexicon_model
        lf = lm.formula
        pfi = lf.pfInterface

        def get_lex_node_str(le):
            _, a, b = lm.get_lexical_entry_components(le, LaTeX=True)
            return (b, ','.join(a))

        ic_labels = {ic_label:"I_{%d}"%(idx) for idx, ic_label in enumerate(self.grammar.ic2df.keys())}
        lex_nodes = {x: get_lex_node_str(le) for x, le in lm.lexical_entries.items()}
        crossings = self.crossings

        def cleanup_heading(x):
            rs = [("C_question", "{C}_{ques.}"),
                  ("C_declarative", "{C}_{decl.}"),
                  ("~", "\sim")]
            for (a, b) in rs:
                x = x.replace(a, b)
            return f"${x}$"

        def get_col_vec(ic_label, lex_nodes):
            return [1 if crossings[(ic_label, lex_node)] > 0 else 0
                    for lex_node in lex_nodes]

        def get_row_vec(lex_node, ic_labels):
            return [1 if crossings[(ic_label, lex_node)] > 0 else 0
                    for ic_label in ic_labels]

        def score_vec(vec):
            return sum([(1 if v else 0)*(2**i) for i, v in enumerate(vec)])

        px = list(ic_labels.keys())
        lx = list(lex_nodes.keys())

        px = list(sorted(px, key=lambda ic_label: score_vec(get_col_vec(ic_label, lx))))
        lx = list(sorted(lx, key=lambda lex_node: score_vec(get_row_vec(lex_node, px))))

        # Seriate the rows and columns.
        p_ser_idx = seriate(pdist([get_col_vec(x, lx) for x in px], metric='hamming'))
        l_ser_idx = seriate(pdist([get_row_vec(x, px) for x in lx], metric='hamming'))

        seriated_px = [px[i] for i in p_ser_idx]
        seriated_lx = [lx[i] for i in l_ser_idx]

        clustered_seriated_px = []
        if self.cluster_input_sentences:
            for p_node in seriated_px:
                for cluster in clustered_seriated_px:
                    q_node = cluster[0]
                    p_vec = [crossings[(p_node, l_node)] for l_node in seriated_lx]
                    q_vec = [crossings[(q_node, l_node)] for l_node in seriated_lx]
                    if p_vec == q_vec:
                        cluster.append(p_node)
                        break
                else:
                    clustered_seriated_px.append([p_node])
        else:
            clustered_seriated_px = seriated_px

        def get_cluster_title_str(cluster):
            if len(cluster) == 1:
                ic_label = cluster[0]
                return f"${ic_labels[ic_label]}$"
            else:
                return "$\{" + ', '.join([v for k, v in ic_labels.items() if k in cluster]) + "\}$"

        title_row = [] if not include_index else ["~"]
        title_row += [r"\rotatebox{0}{" + get_cluster_title_str(cluster).replace("ε","$\epsilon$") + "}"
                     for cluster in clustered_seriated_px]

        rows = []
        for i, l_node in enumerate(seriated_lx, start=1):
            cat_str, le_str = lex_nodes[l_node]
            row = [] if not include_index else ["%d"%(i)]
            row += [cleanup_heading(cat_str), cleanup_heading(le_str)]
            for cluster in clustered_seriated_px:
                p_node = cluster[0]
                c_value = crossings[(p_node, l_node)]
                if self.display_counts:
                    row.append(r"$%d$"%(c_value) if c_value > 0 else r"$\cdot$")
                else:
                    row.append(r"$\pmb{\times}$" if c_value else r"$\cdot$")
            rows.append(row)

        table_str = "\n".join([r" & ".join(row) + r" \\" for row in rows])
        return LATEX_DOC_TEMPLATE%("lll" + "c"*(len(title_row)+1),
                                   str(len(ic_labels)),
                                   str(len(ic_labels)+3),
                                   " & ".join(title_row),
                                   table_str)
