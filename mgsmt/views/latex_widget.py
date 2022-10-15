#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from z3 import *

import ipywidgets as widgets
from ipywidgets import interact
from ipywidgets import Label, HBox, VBox

from IPython.core.display import display, HTML


class LaTeXWidget:

    def __init__(self, latex_view_obj, label, dir_name):

        self.latex_view_obj = latex_view_obj
        self.dir_name = dir_name
        self.label = label

        def on_ui_update(**args):
            # A callback that is executed whenever an element of the GUI is updated
            # by the user.
            self.on_ui_update(args)

        self.ui = self.get_layout()
        self.out = widgets.interactive_output(on_ui_update,
                                              {'img_view': self.img_view,
                                               'source_view': self.source_view,
                                               'log_view': self.log_view})


    def on_ui_update(self, args):
        pass


    def get_layout(self):
        basic_layout = widgets.Layout(flex='1', border='solid 1px grey', padding='3px')
        invisible_layout = widgets.Layout(flex='1', padding='6px')

        def heading(text, size=5):
            assert 1 <= size <= 5
            return widgets.HTML(value="<h%d><u>%s</u></%d>"%(size, text, size))

        # Contents of the Rendered Image tab.
        img_filename = self.latex_view_obj.display(dir_name=self.dir_name,
                                                   file_name="%s_lexicon"%(self.label))
        with open(img_filename, 'rb') as f_in:
            img = copy.deepcopy(f_in.read())

        self.img_view = widgets.Image(value=img,
                                      format='png',
                                      layout=widgets.Layout(flex='1', height='400px'))
        self.img_filename_textarea = widgets.Text(value=img_filename,
                                                  disabled=False,
                                                  layout={'width': '95%'})
        self.img_box = widgets.VBox([widgets.HBox([widgets.Label("File: "),
                                                   self.img_filename_textarea],
                                                   layout=invisible_layout),
                                     self.img_view],
                                    layout=invisible_layout)

        # Contents of the Source tab.
        self.src_filename_text = widgets.Text(value=self.latex_view_obj.latex_source_filepath,
                                              disabled=False,
                                              layout={'width': '95%'})
        self.source_view = widgets.Textarea(value=self.latex_view_obj.get_latex_source(),
                                            disabled=False,
                                            layout=widgets.Layout(flex='1',
                                                                  height='400px',
                                                                  width='100%'))
        self.source_box = widgets.VBox([widgets.HBox([widgets.Label("File: "),
                                                      self.src_filename_text],
                                                     layout=invisible_layout),
                                        self.source_view],
                                       layout=invisible_layout)

        # Contents of the Log tab.
        log_filename = '.'.join(img_filename.split('.')[:-1]) + '.log'
        with open(log_filename, 'r') as f_in:
            log_text = ''.join(f_in.readlines())

        self.log_view = widgets.Textarea(value=log_text,
                                         disabled=False,
                                         layout=widgets.Layout(flex='1', height='400px', width='100%'))

        # Construct the tabs widget.
        self.tabs = widgets.Tab(children=[self.img_box, self.source_box, self.log_view])
        self.tabs.set_title(0, 'Rendered View')
        self.tabs.set_title(1, 'LaTeX Source')
        self.tabs.set_title(2, 'Log')

        return self.tabs


    def display(self):
        display(self.ui, self.out)
