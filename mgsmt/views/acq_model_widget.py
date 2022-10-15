#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#
from z3 import *

import mgsmt
import mgsmt.views.modeltableview
import mgsmt.views.derivationmodeltreeview
import mgsmt.views.derivationmodelnodeseqview
from mgsmt.solver.solver_utils import distinct, ordered, same_node

import ipywidgets as widgets
from ipywidgets import interact
from ipywidgets import Label, HBox, VBox

from itertools import product
from collections import OrderedDict
import tempfile

from IPython.core.display import display, HTML
#------------------------------------------------------------------------------#

class GrammarWidget:
    def __init__(self, grammar):
        self.lexicon_model = grammar.lexicon_model
        self.derivation_models = grammar.derivation_models

        # Constituent widgets.
        self.widgets = {}

        # Display all visualization options on the bottom.

        # Display the lexicon and its statistics on the left.
        lex_lines = self.lexicon_model.pp_str_repr()
        self.lexicon = widgets.Textarea(value='\n'.join(lex_lines),
                                        disabled=True,
                                        rows=20)

        # Display the sentence and its derivation on the right.
        self.sent_choices = OrderedDict()
        for k, v in grammar.derivation_models.items():
            self.sent_choices[k] = {}
            self.sent_choices[k]['sentence'] = v.get_sentence()
            self.sent_choices[k]['img_filepath'] = {}
            self.sent_choices[k]['dmtv'] = mgsmt.views.derivationmodeltreeview.DerivationModelTreeView(derivation_model=v,
                                                                   lexicon_model=grammar.lexicon_model)
            self.sent_choices[k]['dmnsv'] = mgsmt.views.derivationmodelnodeseqview.DerivationModelNodeSeqView(derivation_model=v,
                                                                       lexicon_model=grammar.lexicon_model)

        default_sent_key = next(iter(self.sent_choices.keys()))
        sentences = {v['sentence'] for v in self.sent_choices.values()}
        self.sentences = widgets.Select(options=sentences,
                                        value=self.sent_choices[default_sent_key]['sentence'],
                                        disabled=False,
                                        rows=20)

        self.derivation_view = widgets.Image(value=self.get_derivation_img(default_sent_key), format='png')
        self.dview_title = widgets.HTML(value='<I>No sentence selected...</I>')
        self.__init_derivation_view_options__()

        self.nodeseq_view = widgets.Image(value=self.get_nodeseq_img(default_sent_key), format='png')
        self.nsview_title = widgets.HTML(value='<I>No sentence selected...</I>')
        self.__init_node_seq_view_options__()

        self.constraint_table_view = widgets.HTML(
            value="<b>Coming Soon!</b>",
            placeholder='HTML Error!')

        self.view_options = widgets.Box([])

        def on_ui_update(**args):
            """
            A callback that is executed whenever an element of the GUI is updated by the user.
            """
            k = self.get_sent_key(args['sentence'])
            title_template = '<H4><CENTER><B>Sentence: </B>"%s"</CENTER></H4>'
            # Update the Derivation View.
            if args['dview_display_sent_checkbox']:
                self.dview_title.value = title_template%(self.sent_choices[k]['sentence'])
            else:
                self.dview_title.value = ''
            dmtv = self.sent_choices[k]['dmtv']
            dmtv.label_display_mode = args['dview_node_content_dropdown']
            dmtv.display_head_movement_arrows_checkbox = args['dview_display_head_movement_arrows_checkbox']
            dmtv.display_phrasal_movement_arrows_checkbox = args['dview_display_phrasal_movement_arrows_checkbox']
            self.derivation_view.value = self.get_derivation_img(k, update=True)
            # Update the Node Seq View.
            dmnsv = self.sent_choices[k]['dmnsv']
            if args['nsview_display_sent_checkbox']:
                self.nsview_title.value = title_template%(self.sent_choices[k]['sentence'])
            else:
                self.nsview_title.value = ''
            dmnsv.label_display_mode = args['nsview_node_content_dropdown']
            dmnsv.nsview_display_box_around_seqs = args['nsview_display_box_around_seqs']
            dmnsv.display_head_movement_arrows = args['nsview_display_head_movement_arrows_checkbox']
            dmnsv.display_phrasal_movement_arrows = args['nsview_display_phrasal_movement_arrows_checkbox']
            dmnsv.display_arrows_to_inactive_nodes = args['nsview_display_arrows_to_inactive_nodes']
            dmnsv.display_null_node = args['nsview_display_null_node']
            self.nodeseq_view.value = self.get_nodeseq_img(k, update=True)

        self.ui = self.get_layout()
        self.out = widgets.interactive_output(on_ui_update, {
            'sentence': self.sentences,
            'dview_node_content_dropdown': self.dview_node_content_dropdown,
            'dview_display_sent_checkbox': self.dview_display_sent_checkbox,
            'dview_display_head_movement_arrows_checkbox': self.dview_display_head_movement_arrows_checkbox,
            'dview_display_phrasal_movement_arrows_checkbox': self.dview_display_phrasal_movement_arrows_checkbox,
            'nsview_node_content_dropdown': self.nsview_node_content_dropdown,
            'nsview_display_sent_checkbox': self.nsview_display_sent_checkbox,
            'nsview_display_box_around_seqs': self.nsview_display_box_around_seqs,
            'nsview_display_head_movement_arrows_checkbox': self.nsview_display_head_movement_arrows_checkbox,
            'nsview_display_phrasal_movement_arrows_checkbox': self.nsview_display_phrasal_movement_arrows_checkbox,
            'nsview_display_arrows_to_inactive_nodes': self.nsview_display_arrows_to_inactive_nodes,
            'nsview_display_null_node': self.nsview_display_null_node_checkbox
            })

    def __init_derivation_view_options__(self):
        self.dview_node_content_dropdown = widgets.Dropdown(
            options=['Lexical Item', 'Node-Sequence Index', 'Phonetic Form', 'Node Subset', 'Nothing'],
            value='Lexical Item',
            description='Contents of nodes:',
            style={'description_width': 'initial'},
            layout={'width': 'initial'},
            disabled=False)

        self.dview_display_sent_checkbox = widgets.Checkbox(
            value=True,
            description='Display Sentence',
            indent=False)

        self.dview_display_phrasal_movement_arrows_checkbox = widgets.Checkbox(
            value=True,
            description='Display Phrasal Movement Arrows',
            indent=False)

        self.dview_display_head_movement_arrows_checkbox = widgets.Checkbox(
            value=True,
            description='Display Head Movement Arrows',
            indent=False)

    def __init_node_seq_view_options__(self):
        self.nsview_node_content_dropdown = widgets.Dropdown(
            options=['Lexical Item', 'Node-Sequence Index', 'Phonetic Form', 'Node Subset', 'Nothing'],
            value='Phonetic Form',
            description='Contents of nodes:',
            style={'description_width': 'initial'},
            layout={'width': 'initial'},
            disabled=False)

        self.nsview_display_sent_checkbox = widgets.Checkbox(
            value=True,
            description='Display Sentence',
            indent=False)

        self.nsview_display_box_around_seqs = widgets.Checkbox(
            value=False,
            description='Display Box Around Node Sequences',
            disabled=True,
            indent=False)

        self.nsview_display_phrasal_movement_arrows_checkbox = widgets.Checkbox(
            value=True,
            description='Display Phrasal Movement Arrows',
            indent=False)

        self.nsview_display_head_movement_arrows_checkbox = widgets.Checkbox(
            value=True,
            description='Display Head Movement Arrows',
            indent=False)

        self.nsview_display_arrows_to_inactive_nodes = widgets.Checkbox(
            value=False,
            description='Display Arrows to Inactive Nodes.',
            indent=False)

        self.nsview_display_null_node_checkbox = widgets.Checkbox(
            value=True,
            description='Display the Bottom (nullary) node',
            indent=False)


    def get_sent_key(self, sentence):
        for k, v in self.sent_choices.items():
            if v['sentence'] == sentence:
                return k
        raise Exception()


    def get_derivation_img(self, sent_key, update=False):
        fps = self.sent_choices[sent_key]['img_filepath']
        if update:
            fps.pop('derivation', None)
        if 'derivation' not in fps:
            _, fps['derivation'] = tempfile.mkstemp(suffix='.png')
            self.sent_choices[sent_key]['dmtv'].img(output_filepath=fps['derivation'], img_format='png')
        with open(fps['derivation'], 'rb') as f_in:
            return copy.deepcopy(f_in.read())


    def get_nodeseq_img(self, sent_key, update=False):
        fps = self.sent_choices[sent_key]['img_filepath']
        if update:
            fps.pop('nodeseq', None)
        if 'nodeseq' not in fps:
            _, fps['nodeseq'] = tempfile.mkstemp(suffix='.png')
            self.sent_choices[sent_key]['dmnsv'].img(output_filepath=fps['nodeseq'], img_format='png')
        with open(fps['nodeseq'], 'rb') as f_in:
            return copy.deepcopy(f_in.read())


    def get_layout(self):
        basic_layout = widgets.Layout(border='solid 1px grey', padding='3px')

        def heading(text, size=5):
            assert 1 <= size <= 5
            return widgets.HTML(value="<h%d><u>%s</u></%d>"%(size, text, size))

        # Derivation Tree View
        dview_tabs = widgets.Tab(children=[
            VBox([heading('Derivation View'), self.derivation_view, self.dview_title], layout=basic_layout),
            VBox([self.dview_node_content_dropdown,
                  self.dview_display_sent_checkbox,
                  self.dview_display_head_movement_arrows_checkbox,
                  self.dview_display_phrasal_movement_arrows_checkbox],
                     layout=basic_layout)])
        dview_tabs.set_title(0, 'Derivation')
        dview_tabs.set_title(1, 'Options')

        # Node-Seq View
        nsview_tabs = widgets.Tab(children=[
            VBox([heading('Node Sequence View'), self.nodeseq_view, self.nsview_title], layout=basic_layout),
            VBox([self.nsview_node_content_dropdown,
                  self.nsview_display_sent_checkbox,
                  self.nsview_display_box_around_seqs,
                  self.nsview_display_head_movement_arrows_checkbox,
                  self.nsview_display_phrasal_movement_arrows_checkbox,
                  self.nsview_display_arrows_to_inactive_nodes,
                  self.nsview_display_null_node_checkbox],
                     layout=basic_layout)])
        nsview_tabs.set_title(0, 'Node Sequences')
        nsview_tabs.set_title(1, 'Options')

        # Assemble it all together.
        tabs = widgets.Tab(children=[
            HBox([VBox([heading('Lexicon'), self.lexicon], layout=basic_layout),
                  VBox([heading('Sentence'), self.sentences], layout=basic_layout),
                  dview_tabs,
                  nsview_tabs,
#                  tableview_tabs,
                  ],
                 layout=basic_layout),
            VBox([heading('TODO: Fill me in!'), self.view_options], layout=basic_layout)],
            layout=basic_layout)
        tabs.set_title(0, 'Grammar')
        tabs.set_title(1, 'Options')
        return tabs

    def display(self):
        display(self.ui, self.out)
