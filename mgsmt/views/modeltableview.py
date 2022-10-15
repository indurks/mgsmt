#!/usr/bin/env python3
# -*- coding: utf-8 -*-


__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from IPython.core.display import display, HTML
import tabulate

class ModelTableView:

    def __init__(self):
        pass

    def display_table(self, rows, headers, title=""):
        html = tabulate.tabulate(rows, headers=headers, tablefmt='html')
        title_str = '<caption><big><b>Table.</b> <i>%s</i></big></caption>'%(title)
        html = html.replace('<thead>', title_str + '<thead>')
        display(HTML(html))
