#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2019-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import importlib

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
\multirow{2}{*}{ID} & \multirow{2}{*}{Category} & \multirow{2}{*}{Features} & \multicolumn{%s}{c}{Phonological Forms} \\
\cline{4-%s}
& & %s \\
\midrule
%s
\bottomrule
\end{tabular}
}
{\small
\caption{Model Output -- A \emph{Factored} View of the Inferred Lexicon. 
Each row indicates the phonological forms that are paired with the listed 
category and features in the lexicon. The rows and columns have been seriated 
(using the hamming distance metric) so as to visually group together similar 
entries. There are %d distinct overt phonological forms in the lexicon.}
}
\end{figure}
\end{landscape}
\end{document}
"""

class FactoredLexiconLaTeXView:

    def __init__(self, grammar):
        self.grammar = grammar
        self.crossings = grammar.lexicon_model.get_pf_lexicon_crossing_occurrences()
        self.latex_source_filepath = None


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
        #m_eval = lm.model.evaluate

        def get_lex_node_str(le):
            _, a, b = lm.get_lexical_entry_components(le, LaTeX=True)
            return (b, ','.join(a))

        pf_nodes = {x: pfi.get_pf(x) for x in pfi.non_null_nodes()}
        lex_nodes = {x: get_lex_node_str(le) for x, le in lm.lexical_entries.items()}
        crossings = self.crossings

        def cleanup_heading(x):
            rs = [("C_question", "{C}_{ques.}"),
                  ("C_declarative", "{C}_{decl.}"),
                  ("~", "\sim")]
            for (a, b) in rs:
                x = x.replace(a, b)
            return f"${x}$"

        def get_col_vec(pf_node, lex_nodes):
            return [1 if crossings[(pf_node, lex_node)] else 0
                    for lex_node in lex_nodes]

        def get_row_vec(lex_node, pf_nodes):
            return [1 if crossings[(pf_node, lex_node)] else 0
                    for pf_node in pf_nodes]

        def score_vec(vec):
            return sum([(1 if v else 0)*(2**i) for i, v in enumerate(vec)])

        px = list(pf_nodes.keys())
        lx = list(lex_nodes.keys())
        
        px = list(sorted(px, key=lambda pf_node: score_vec(get_col_vec(pf_node, lx))))
        lx = list(sorted(lx, key=lambda lex_node: score_vec(get_row_vec(lex_node, px))))
        
        # Seriate the rows and columns.
        p_ser_idx = seriate(pdist([get_col_vec(x, lx) for x in px], metric='hamming'))
        l_ser_idx = seriate(pdist([get_row_vec(x, px) for x in lx], metric='hamming'))
        
        seriated_px = [px[i] for i in p_ser_idx]
        seriated_lx = [lx[i] for i in l_ser_idx]
        
        title_row = [] if not include_index else ["~"]
        title_row += [r"\rotatebox{90}{" + pf_nodes[pf_node].replace("ε","$\epsilon$") + "\hspace{1em}}"
                     for pf_node in seriated_px]

        rows = []
        for i, l_node in enumerate(seriated_lx, start=1):
            cat_str, le_str = lex_nodes[l_node]
            row = [] if not include_index else ["%d"%(i)]
            row += [cleanup_heading(cat_str), cleanup_heading(le_str)]
            for p_node in seriated_px:
                row.append(r"$\pmb{\times}$" if crossings[(p_node, l_node)] else r"$\cdot$")
                #row.append("X" if crossings[(p_node, l_node)] else "-")
            rows.append(row)

        table_str = "\n".join([r" & ".join(row) + r" \\" for row in rows])
        num_distinct_overt_pf = len(list(filter(lambda x: "ε" not in pf_nodes[x],
                                                seriated_px)))
        return LATEX_DOC_TEMPLATE%("ccc" + "l"*(len(title_row)+1),
                                   str(len(pf_nodes)),
                                   str(len(pf_nodes)+3),
                                   " & ".join(title_row),
                                   table_str,
                                   num_distinct_overt_pf)
