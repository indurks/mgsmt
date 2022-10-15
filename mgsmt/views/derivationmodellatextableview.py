#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from z3 import *
import mgsmt
from mgsmt.views.modeltableview import ModelTableView

class DerivationModelTableView(ModelTableView):

    def __init__(self, derivation_model, lexicon_model=None):
        super()
        self.dm = derivation_model
        self.nodes = list(self.dm.formula.all_nodes())

        # TODO: Rename this "eval" function as it overrides a python built-in
        # fn.
        eval, df = self.dm.model.evaluate, self.dm.formula

        def pp_node_type(node):
            mapping = [
                (df.ntype_null, '∅'),
                (df.ntype_overt_lexical, '(Overt) Lexical'),
                (df.ntype_covert_lexical, '(Empty) Lexical'),
                (df.ntype_intermediate, 'Intermediate'),
                (df.ntype_root, 'Root')
            ]
            for t, t_str in mapping:
                if eval(t == df.node_type(node)):
                    return t_str
            raise Exception("%r not in %r"%(node, df.formula_name))

        def get_node_id(node):
            s = str(node)
            # extract the node id
            node_id = int(s.split('_')[-1])
            assert 0 <= node_id
            return node_id

        def pp_node_label(node):
            node_id = get_node_id(node)
            if node_id == 0:
                return '∅'
            elif node_id == len(self.nodes) - 1:
                return 'Root'
            return "%d"%(node_id)

        def get_sister_node(d_node):
            # Find the node it merged with
            for sister in df.nodes():
                if eval(df.merged(d_node, sister) != df.null_node):
                    return pp_node_label(sister)
            return None

        def get_lexicon_node(d_node):
            if lexicon_model == None:
                return None
            return eval(lexicon_model.formula.derivations[df.formula_name]['bus'](d_node))

        def get_lexical_entry(d_node):
            return self.dm.get_lex_entry_str(d_node, lexicon_model)

        self.column_scheme = [
            ('ID', lambda x: get_node_id(x)),
            ('Label', lambda x: pp_node_label(x)),
            ('Type', lambda x: pp_node_type(x)),
            ('Phonetic Form', lambda x: df.pfInterface.get_pf(eval(df.pf_map(x)))),
            ('Lexical Entry', lambda x: get_lexical_entry(x)),
            ('Head', lambda x: pp_node_label(eval(df.head(x)))),
            ('Parent', lambda x: pp_node_label(eval(df.parent(x)))),
            ('Sister', lambda x: get_sister_node(x)),
            ('Move To', lambda x: pp_node_label(eval(df.move_loc(x)))),
            ('Head-Movement To', lambda x: pp_node_label(eval(df.head_movement(x)))),
            ('Projects', lambda x: eval(df.projects(x))),
            ('Lexicon Node', lambda x: get_lexicon_node(x)),
        ]

        self.headers = [header for (header, _) in self.column_scheme]
        self.rows = [[fn(node) for (_, fn) in self.column_scheme]
                     for node in self.nodes]

    def print_table(self):
        title = "Derivation Model %s"%(self.dm.formula.formula_name)
        super().display_table(rows=self.rows,
                              headers=self.headers,
                              title=title)
