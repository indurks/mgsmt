#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import random, tempfile
from itertools import product

from z3 import *

import mgsmt
from mgsmt.solver.solver_utils import distinct, ordered, same_node

import IPython

class DerivationModelNodeSeqView(object):

    def __init__(self, derivation_model, lexicon_model=None):
        self.dm = derivation_model
        self.df = self.dm.formula
        self.lexicon_model = lexicon_model
        self.label_display_mode = 'Phonetic Form'
        self.display_head_movement_arrows = True
        self.display_phrasal_movement_arrows = True
        self.display_arrows_to_inactive_nodes = False
        self.display_null_node = True
        self.display_nodeseq_clusters = True

    def graphviz_repr(self,
                      display_node_id=False,
                      head_relabeling_map={},
                      head_coloring_map={},
                      k_node_spacing=1.5):
        import pygraphviz
        g = pygraphviz.AGraph(directed=True, strict=False, overlap=False, splines='spline')
        m_eval, df = self.dm.model.evaluate, self.dm.formula
        node_id = str

        # Add the nodes.
        def node_label(x, null_node_lbl='⊥'):
            if self.label_display_mode == 'Nothing':
                label = ''
            elif self.label_display_mode == 'Phonetic Form':
                if m_eval(x == df.null_node):
                    return null_node_lbl
                elif m_eval(df.head(x) == df.null_node):
                    return ''
                return self.dm.get_decorated_pf(m_eval(df.head(x)), display_head_movement=False)
            else:
                raise NotImplementedError()

        def node_style(x):
            style = 'filled'
            if not(m_eval(df.is_lexical(x))):
                style += ',rounded'
            if m_eval(Or([And(df.move_loc(y) == x, df.head(x) != df.null_node) for y in df.nodes()])):
                style += ',dashed'
            return style

        def add_node(x, pos, shape='circle'):
            g.add_node(node_id(x),
                       label=node_label(x),
                       shape=shape,
                       style=node_style(x),
                       fillcolor=self.dm.get_color_of_head(m_eval(df.head(x))),
                       pos=pos)

        num_node_seqs = len(list(df.node_seqs()))
        max_num_feats = max(len(list(ns)) for ns in df.node_seqs())
        add_node(df.root_node, pos='%f,%f!'%(k_node_spacing * (num_node_seqs-1)/2.0, k_node_spacing * max_num_feats))

        for (i, seq) in enumerate(df.node_seqs()):
            for (j, x) in enumerate(seq):
                add_node(x, pos='%f,%f!'%(k_node_spacing*i, k_node_spacing*j))

        if self.display_null_node:
            add_node(df.null_node, pos='%f,%f!'%(k_node_spacing * (num_node_seqs-1)/2.0, -1))

        # Add the edges.
        def add_edges_for_func(fn, fn_label, nodes, style='solid', color='black'):
            for x in nodes:
                if m_eval(df.head(x) == df.null_node):
                    continue
                elif not(self.display_arrows_to_inactive_nodes and self.display_null_node):
                    if m_eval(fn(x) == df.null_node):
                        continue
                idX, idY = (node_id(x), node_id(m_eval(fn(x))))
                g.add_edge(idX, idY, key="{}_{}_{}".format(fn_label, idY, idX), style=style, color=color)

        add_edges_for_func(df.parent, 'parent', nodes=df.nodes(), style='solid')
        if self.display_phrasal_movement_arrows:
            add_edges_for_func(df.move_loc, 'move_loc', nodes=df.nodes(), style='dashed')
        if self.display_head_movement_arrows:
            add_edges_for_func(df.head_movement, 'head_movement', nodes=df.lex1nodes(), style='dotted')
        return g

    def img(self, output_filepath, img_format):
        assert img_format in ('png', 'svg', 'pdf')
        assert output_filepath.endswith(img_format)
        self.graphviz_repr().draw(output_filepath, prog='fdp')
        #return open(output_filepath, 'rb')

    def display(self, output_filepath):
        with tempfile.TemporaryDirectory() as tmpdirname:
            if output_filepath is None:
                output_filepath = '%s/blah.%s'%(tmpdirname, img_format)
            self.img(output_filepath=output_filepath, img_format='svg')
            IPython.display.display(IPython.display.SVG(output_filepath))
