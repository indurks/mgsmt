#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Tabular display of a Derivation Model.
"""

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from z3 import *
import mgsmt
from mgsmt.views.modeltableview import ModelTableView
import mgsmt.views.view_utils as view_utils

from IPython.display import display, Math, Image
import contextlib, os, shutil, subprocess, time, uuid

LATEX_DOC_TEMPLATE = r"""\documentclass{article}
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
\caption{%s}
}
\end{table}
\end{landscape}
\end{document}
"""


LATEX_CAPTION_TEMPLATE = r"""Model interpretation for the parse of sentence \#%d (of %d) from the
input sequence: ``%s''. Values are supplied for each of the uninterpreted
functions, that together make up the model of the parse: $\mathfrak{H}$ (head),
$\mathfrak{P}$ (parent), $\mathfrak{M}_P$ (phrasal movement) and $\mathfrak{M}_H$
(head movement). The \emph{Node Type} indicates the role of the node within
the parse tree. The Root node is a non-leaf node. The Bottom node plays the
role of a null value that the uninterpreted functions can map to when they do
not point to a node that is in the tree -- e.g. the head of a node that is not
used in the parse tree is the Bottom node. Each node $D_i$ is a member of the 
finite sort $D$ (note that not all of the members of the sort $D$ are used). 
The Node Label and Type are with reference to the associated node in the
parse tree.
"""


class DerivationModelTableView(ModelTableView):

    def __init__(self, derivation_model, sent_idx, num_sents, sent, lexicon_model=None):
        super()
        self.dm = derivation_model
        self.nodes = list(self.dm.formula.all_nodes())
        self.sent_idx = sent_idx
        self.num_sents = num_sents
        self.sent = sent

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
                ([df.root_node], 'Root')
            ]
            for ns, t_str in mapping:
                for n in ns:
                    if z3eval(n == node):
                        return t_str
            else:
                raise Exception("%r not in %r"%(node, df.formula_name))

        def get_id_from_node(node):
            return int(str(node).split('_')[-1])

        def node_id(node, sort='D'):
            node_id = get_id_from_node(node)
            assert 0 <= node_id
            return "$%s_{%d}$"%(sort, node_id)

        def lex_node_str(d_node):
            if lexicon_model is None:
                return None
            bus = lexicon_model.formula.derivations[df.formula_name]['bus']
            return node_id(z3eval(bus(d_node)), sort='L')

        def lex_node_succ_str(d_node):
            if lexicon_model is None:
                return None
            bus = lexicon_model.formula.derivations[df.formula_name]['bus']
            succ = lexicon_model.formula.succ
            return node_id(z3eval(succ(bus(d_node))), sort='L')


        def lex_entry_str(d_node):
            replacements = [('∅', '\emptyset'),
                            ('·', ' \cdot '),
                            ('ε', r'\epsilon'),
                            ("C_declarative", "C_{decl.}"),
                            ("C_question", "C_{ques.}"),
                            ('~', r'{\sim}')]
            le_str = self.dm.get_lex_entry_str(d_node, lexicon_model, HTML=False, LaTeX=True)
            fixed_le_str = str_replace_reduce(le_str, replacements)
            return "$%s$"%(fixed_le_str if fixed_le_str else "$~$")            

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
            ('Node', node_id),
#            ('Node Type', node_type_str),
#            ('PForm', pform_str),
            ('Label', lex_entry_str),                              
            (r'$\beta(D_i)$', cat_str),
            ('$\mathfrak{H}(D_i)$',   lambda x: node_id(z3eval(df.head(x)))),
            ('$\mathfrak{P}(D_i)$', lambda x: node_id(z3eval(df.parent(x)))),
            ('$M_{P}(D_i)$', lambda x: node_id(z3eval(df.move_loc(x)))),
            ('$M_{H}(D_i)$', lambda x: node_id(z3eval(df.head_movement(x)))),
            ('$\mu(D_i)$', lex_node_str),
            ('$\psi(\mu(D_i))$', lex_node_succ_str)
        ]

        self.headers = [header for (header, _) in self.column_scheme]
        handle_empty_entry = lambda e: e if e else "~"
        self.rows = [[handle_empty_entry(fn(node)) for (_, fn) in self.column_scheme]
                     for node in sorted(self.nodes, key=lambda k: get_id_from_node(k))]


    def print_table(self):
        raise NotImplementedError
        title = "Derivation Model %s"%(self.dm.formula.formula_name)
        super().display_table(rows=self.rows, headers=self.headers, title=title)


    def display(self, dir_name, file_name):
        self.latex_source_filepath = dir_name + '/' + file_name + '.tex'
        return view_utils.display_latex(self.get_latex_source(),
                                        dir_name,
                                        file_name,
                                        visualize=False,
                                        include_rotation=True)


    def get_latex_source(self, verbose=False):
        col_str = "".join('l' for _ in self.headers)
        col_name_str = " & ".join(self.headers)
        row_strs = [" & ".join(row) + " \\\\ \n" for row in self.rows]
        table_str = " ".join(row_strs)
        caption_str = LATEX_CAPTION_TEMPLATE%(self.sent_idx, self.num_sents, self.sent)
        doc_str = LATEX_DOC_TEMPLATE%(col_str, col_name_str, table_str, caption_str)
        if verbose:
            print(doc_str)
        return doc_str
