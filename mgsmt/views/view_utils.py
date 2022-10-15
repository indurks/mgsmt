#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2019-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

import contextlib, importlib, os, subprocess
from IPython.display import display, Math, Image

import mgsmt
import mgsmt.views
import mgsmt.views.lexiconmodeltableview
import mgsmt.views.lexiconmodellatexview
import mgsmt.views.factored_lexicon_view
import mgsmt.views.derivationmodeltableview
#importlib.reload(mgsmt.views.derivationmodeltableview)
import mgsmt.views.derivation_tree_latex_view
import mgsmt.views.derivationmodeltreeview
import mgsmt.views.latex_widget
import mgsmt.views.multi_latex_widget
import mgsmt.views.wisdom_latex_view
import mgsmt.views.optimization_stack_latex_view

import mgsmt.views.lexiconmodeltableview as lexiconmodeltableview
from mgsmt.views.lexiconmodellatexview import LexiconModelLaTeXView
from mgsmt.views.factored_lexicon_view import FactoredLexiconLaTeXView
from mgsmt.views.derivationmodeltreeview import DerivationModelTreeView
from mgsmt.views.derivation_tree_latex_view import DerivationTreeLaTeXView
from mgsmt.views.derivationmodeltableview import DerivationModelTableView
from mgsmt.views.latex_widget import LaTeXWidget
from mgsmt.views.multi_latex_widget import MultiLaTeXWidget
from mgsmt.views.wisdom_latex_view import WisdomLaTeXView

#------------------------------------------------------------------------------#

def display_latex(latex_src,
                  dir_name,
                  file_name,
                  dpi=300,
                  visualize=True,
                  debug=True,
                  include_rotation=False):
    fp = dir_name + '/' + file_name
    with open(f'{fp}.tex', 'w') as f_tex:
        f_tex.write(latex_src)
    rotation_str = " -rotate 90 " if include_rotation else " "
    cmds = [f"pdflatex -output-directory {dir_name} {fp}.tex",
            f"convert -colorspace RGB -density {dpi} {fp}.pdf -flatten -trim{rotation_str}+repage {fp}.png"]
    with contextlib.suppress(subprocess.CalledProcessError):
        for cmd in cmds:
            subprocess.check_call(cmd.split(),
                                  stdout=subprocess.DEVNULL,
                                  stdin=subprocess.DEVNULL)
    img_fp = f"{fp}.png"
    if not os.path.isfile(img_fp):
        with open(f"{fp}.log", 'r') as f_log:
            for line in list(f_log)[-100]:
                print(line, flush=True)
        raise FileNotFoundError(img_fp)
    if visualize:
        display(Image(filename=img_fp, width=1200, height=800))
    with contextlib.suppress(FileNotFoundError):
        os.remove(f"{fp}.aux")
        if not(debug):
            os.remove(f"{fp}.log")
    return img_fp


def display_model_tables(grammar, experiment):
    e = experiment
    # Lexicon Models.
    # lmtv = lexiconmodeltableview.LexiconModelTableView(grammar.lexicon_model)
    # lw_lmtv = LaTeXWidget(lmtv,
    #                       f"lexicon-model",
    #                       experiment.logging_dir)

    # Derivation Models.
    dmtvs = {i:DerivationModelTableView(dm,
                                        i,
                                        len(e.grammar.derivation_models),
                                        repr(dm.formula.whitelisted_surface_forms[0]),
                                        e.grammar.lexicon_model)
             for i, (_, dm) in enumerate(e.grammar.derivation_models.items())}
    lws_dmtvs = [mgsmt.views.LaTeXWidget(dmtv,
                                         f'derivation-model-{i}',
                                         e.logging_img_dir)
                   for i, dmtv in dmtvs.items()]

    # Multi-View LaTeX Widget.
    #lws = [lw_lmtv] + lws_dmtvs
    lws = lws_dmtvs
    mlw = MultiLaTeXWidget(lws, [lw.label for lw in lws], e.logging_img_dir)
    mlw.display()


def display_derivations_and_lexicon(grammar, experiment):
    e = experiment
    # Display figures for the derivation, lexicon and factored lexicon.

    # Derivations.
    dmtvs = [DerivationModelTreeView(dm, lexicon_model=grammar.lexicon_model)
             for df_id, dm in grammar.derivation_models.items()]
    lws_derivations = [LaTeXWidget(DerivationTreeLaTeXView(dmtv),
                                   f'derivation-{i}',
                                   e.logging_img_dir)
                       for i, dmtv in enumerate(dmtvs)]

    # Lexicon.
    lw_lexicon = LaTeXWidget(LexiconModelLaTeXView([grammar.lexicon_model]),
                             'regular-lexicon',
                             e.logging_img_dir)

    # Factored Lexicon.
    factored_lexicon_view = FactoredLexiconLaTeXView(grammar)
    lw_factored_lexicon = LaTeXWidget(factored_lexicon_view,
                                      'factored-lexicon',
                                      e.logging_img_dir)

    lws = [lw_lexicon, lw_factored_lexicon] + lws_derivations
    mlw = MultiLaTeXWidget(lws, [lw.label for lw in lws], e.logging_img_dir)
    mlw.display()


def display_wisdom_history(grammar, experiment):
    e = experiment
    
    oslvs = [mgsmt.views.optimization_stack_latex_view.OptimizationStackLaTeXView(wisdom)
             for wisdom in e.wisdom_history]
    wls = LaTeXWidget(WisdomLaTeXView(e.wisdom_history),
                      'wisdom-history',
                      e.logging_img_dir)
    lws_oslvs = [mgsmt.views.LaTeXWidget(oslv,
                                         f'optimization-stack-{i}',
                                         e.logging_img_dir)
                 for i, oslv in enumerate(oslvs)]
    lws = [wls] + lws_oslvs
    
    mlw = MultiLaTeXWidget(lws, [lw.label for lw in lws], e.logging_img_dir)
    mlw.display()


def display_factorized_lexicon(grammar, experiment):
    raise NotImplemented


def display_factorized_input_sequence(grammar, experiment):
    raise NotImplemented


def display_input_sequence(experiment):
    raise NotImplemented
