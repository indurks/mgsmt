#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import contextlib, random, subprocess, tempfile
from itertools import product

from z3 import *

import mgsmt
from mgsmt.solver.solver_utils import distinct, ordered, same_node

import IPython

class DerivationModelTreeView(object):

    def __init__(self, derivation_model, lexicon_model=None):
        self.dm = derivation_model
        self.df = self.dm.formula
        self.lexicon_model = lexicon_model
        self.display_head_movement_arrows_checkbox = True
        self.display_phrasal_movement_arrows_checkbox = True
        self.label_display_mode = 'Lexical Item'

    def graphviz_repr(self):
        m_eval, df = self.dm.model.evaluate, self.dm.formula
        node_id = str

        def get_children(x):
            for c1, c2 in distinct(product(df.non6root6nodes(), repeat=2)):
                if m_eval(x == df.merged(c1, c2)):
                    if m_eval(df.head(c1) == df.head(x)):
                        if m_eval(df.is_lexical(c1)):
                            return (c1, c2)
                        else:
                            return (c2, c1)
            else:
                return ()

        def walk_derivation_tree(x, top=True):
            if top:
                yield x
            yield from get_children(x)
            for c in get_children(x):
                yield from walk_derivation_tree(c, top=False)

        def get_label(x):
            h_x = m_eval(df.head(x))
            if self.label_display_mode == 'Lexical Item':
                return self.dm.get_lex_entry_str(x, lex_model=self.lexicon_model, HTML=True)
            elif self.label_display_mode == 'Phonetic Form':
                return self.dm.get_decorated_pf(h_x, display_head_movement=False)
            elif self.label_display_mode == 'Nothing':
                return ''
            else:
                raise NotImplementedError("Could not recognize or handle: " + self.label_display_mode)

        def get_node_style(x):
            style = 'filled'
            # Check if its a lexical node.
            if not(m_eval(df.is_lexical(x))):
                style += ',rounded'
            # Check if it will undergo movement.
            if any([m_eval(df.move_loc(y) == x) for y in df.nodes()]):
                style += ',dashed'
            return style

        def add_edge(x, fn, fn_label, directed=False, style='solid', arrowhead='none', dir='forward', weight=10000):
            if m_eval(fn(x) != df.null_node):
                idX, idY = (node_id(x), node_id(m_eval(fn(x))))
                xy_key = "{}_{}_{}".format(fn_label, idX, idY)
                g.add_edge(idY, idX, style=style, directed=directed, arrowhead=arrowhead, dir=dir, key=xy_key, weight=weight)

        import pygraphviz
        g = pygraphviz.AGraph(directed=True, strict=False, rankdir='TB')
        g.edge_attr.update(arrowhead='none')
        for x in walk_derivation_tree(df.root_node):
            g.add_node(node_id(x),
                       label=get_label(x),
                       shape='box',
                       style=get_node_style(x),
                       fillcolor=self.dm.get_color_of_head(m_eval(df.head(x))))
            add_edge(x, df.parent, 'parent')
            if self.display_phrasal_movement_arrows_checkbox:
                add_edge(x, df.move_loc, 'move_loc', style='dashed', directed=True, arrowhead='normal', dir='back', weight=0)
            if self.display_head_movement_arrows_checkbox:
                add_edge(x, df.head_movement, 'head_movement', style='dotted', directed=True, arrowhead='normal', dir='back', weight=0)
        return g

    def img(self, output_filepath, img_format):
        assert img_format in ('png', 'svg', 'pdf')
        assert output_filepath.endswith(img_format)
        gviz_repr = self.graphviz_repr()
        if img_format == 'png':
            intermediate_fp = output_filepath[:-3] + 'svg'
            try:
                gviz_repr.draw(intermediate_fp, prog='dot')
            #with contextlib.suppress(subprocess.CalledProcessError):
                svg2png_cmd = f"convert -density 1200 {intermediate_fp} {output_filepath}"
                subprocess.check_call(svg2png_cmd.split(),
                                      stdout=subprocess.DEVNULL,
                                      stdin=subprocess.DEVNULL)
            except:
                print(gviz_repr)
                raise
        else:
            gviz_repr.draw(output_filepath, prog='dot')

        return gviz_repr


    def display(self, output_filepath, visualize=True):
        with tempfile.TemporaryDirectory() as tmpdirname:
            if output_filepath is None:
                output_filepath = '%s/blah.%s'%(tmpdirname, img_format)
            # NOTE: Graphviz can only handle HTML subscripting when rendering
            # to SVG.
            self.img(output_filepath=output_filepath, img_format='svg')
            svg_obj = IPython.display.SVG(output_filepath)
            IPython.display.display(svg_obj)
        return output_filepath
