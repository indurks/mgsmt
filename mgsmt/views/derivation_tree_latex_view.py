#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2019-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

#from z3 import *

import mgsmt
import mgsmt.views
import mgsmt.views.latex_widget
import mgsmt.views.view_utils as view_utils
#from mgsmt.views.view_utils import display_latex

LATEX_DOC_TEMPLATE = r"""
\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{graphicx}
\usepackage{subfig}
\begin{document}
\pagenumbering{gobble}
\begin{figure}[h!]
\centering
%s
%s
\end{figure}
\end{document}
"""

SINGLE_LATEX_GRAPHIC = r"""
\includegraphics[width=0.75\textwidth]{%s}
"""

DOUBLE_LATEX_GRAPHIC = r"""
\subfloat[Correct]{{\includegraphics[width=5cm]{%s} }}
\qquad
\subfloat[Overgeneration]{{\includegraphics[width=5cm]{%s} }}
"""

SINGLE_LATEX_CAPTION = r"""
\caption{An MG parse for the sentence ``%s''.
The feature sequences displayed in non-leaf nodes have a dot,
$\ \cdot\ $, separating features that have already been consumed (on
the left) from those that have not (on the right).
Dashed arrows denote phrasal movement.
Dotted arrows denote head movement.
Nodes with the same \emph{head} have the same color. 
The parse is assembled in a bottom-up manner via repeated application 
of merge.}
"""

class DerivationTreeLaTeXView:

    def __init__(self,
                 derivation_model_tree_view,
                 secondary_derivation_model_tree_view=None):
        self.dmtv = derivation_model_tree_view
        self.secondary_derivation_model_tree_view = secondary_derivation_model_tree_view


    def display(self, dir_name, file_name, img_format='png'):
        # Render the tree using graphviz.
        self.dot_fp = f"{dir_name}/{file_name}.dot"
        self.img_fp = f"{dir_name}/{file_name}.{img_format}"
        self.gviz_obj = self.dmtv.img(self.img_fp, img_format=img_format)
        self.gviz_src = str(self.gviz_obj)

        # Compile the LaTeX document with the tree as a figure.
        self.latex_source_filepath = f"{dir_name}/{file_name}.tex"
        return view_utils.display_latex(self.get_latex_source(),
                                        dir_name,
                                        file_name,
                                        dpi=1200,
                                        visualize=False,
                                        include_rotation=False)


    def get_latex_source(self):
        IMG_FP = self.img_fp[2:] if self.img_fp.startswith('./') else self.img_fp
        LATEX_GRAPHIC = SINGLE_LATEX_GRAPHIC%(IMG_FP)
        if self.secondary_derivation_model_tree_view:
            LATEX_GRAPHIC = DOUBLE_LATEX_GRAPHIC%(IMG_FP, IMG_FP)
        sent_str = ' '.join(self.dmtv.df.get_surface_forms())
        LATEX_CAPTION = SINGLE_LATEX_CAPTION%(sent_str)
        return LATEX_DOC_TEMPLATE%(LATEX_GRAPHIC, LATEX_CAPTION)
