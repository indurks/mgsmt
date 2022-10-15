#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from z3 import *

import mgsmt
import mgsmt.views
import mgsmt.views.latex_widget
from mgsmt.views.latex_widget import LaTeXWidget

from functools import lru_cache

import ipywidgets as widgets
from ipywidgets import interact

from IPython.core.display import display, HTML

#------------------------------------------------------------------------------#

class MultiLaTeXWidget(LaTeXWidget):

    def __init__(self, latex_view_objs, labels, dir_name):
        self.latex_view_objs = latex_view_objs
        self.labels = labels
        self.labels_to_selection_idx = {lbl:i for i, lbl in enumerate(self.labels)}
        self.dir_name = dir_name

        def on_ui_update(**args):
            selection_idx = self.labels_to_selection_idx[args['select']]
            #for lvo in self.latex_view_objs:
            #    lvo.on_ui_update(args)
            self.latex_view_objs[selection_idx].on_ui_update(args)
            self.tabs = self.latex_view_objs[selection_idx].get_layout()
            self.ui_hbox.children = (self.selection_box, self.tabs)

        self.ui = self.get_layout()
        self.out = widgets.interactive_output(on_ui_update,
                                              {'select': self.select_widget})


    def get_layout(self):
        basic_layout = widgets.Layout(flex='1',
                                      border='solid 1px grey',
                                      padding='3px')
        self.select_widget = widgets.Dropdown(options=self.labels,
                                              value=self.labels[0],
                                              disabled=False)
        self.tabs = self.latex_view_objs[0].get_layout()
        self.selection_box = widgets.HBox([widgets.Label(value="Selection: "),
                                           self.select_widget])
        self.ui_hbox = widgets.VBox([self.selection_box, self.tabs],
                                    layout=basic_layout)
        return self.ui_hbox


    def display(self):
        display(self.ui, self.out)
