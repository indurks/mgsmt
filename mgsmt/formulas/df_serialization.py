#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from itertools import product, chain
from z3 import And, Or, Not, Implies, Xor, Distinct, If, PbEq, PbGe, PbLe
from z3 import BoolSort, Const, Datatype
from mgsmt.formulas.smtformula import SMTFormula
from mgsmt.solver.solver_utils import distinct

import copy, uuid


def deserialize_value(serialized_value, derivation_formula):
    sv = serialized_value
    df = derivation_formula

    if sv[0] == 'Bool':
        assert type(sv[1]) == bool
        return sv[1]
    elif sv[0] == 'DNode':
        if sv[1] == 'root':
            return df.root_node
        elif sv[1] == 'null':
            return df.null_node
        elif sv[1] == 'overt':
            for idx, overt_node_seq in enumerate(df.enum_overt_node_seqs()):
                for j, node in enumerate(overt_node_seq):
                    if idx == sv[2] and j == sv[3]:
                        return node
            else:
                assert False, "Couldn't identify: " + repr(sv) 
        elif sv[1] == 'covert':
            for idx, covert_node_seq in enumerate(df.enum_covert_node_seqs()):
                for j, node in enumerate(covert_node_seq):
                    if idx == sv[2] and j == sv[3]:
                        return node
            else:
                assert False, "Couldn't identify: " + repr(sv) 
    elif sv[0] == 'PFNode':
        return df.pfInterface.get_pf_node(sv[1])
    elif sv[0] == 'CatNode':
        if sv[1] == 'null':
            return df.CatSort.null
        return df.str2cat[sv[1]]

    assert False, sv


def serialize_value(value, derivation_model):
    dm = derivation_model
    df = dm.formula
    
    # Check if it's a boolean value.
    if type(value) == bool:
        return ('Bool', value)

    # Check if it's a member of the derivation-node sort.
    if '_DNode_' in str(value):
        # Check if it's the root node.
        if str(df.root_node) == str(value):
            return ('DNode', 'root')

        # Check if it's the null node.
        if str(df.null_node) == str(value):
            return ('DNode', 'null')

        # Check if it's the overt nodes.
        for idx, overt_node_seq in enumerate(df.enum_overt_node_seqs()):
            for j, node in enumerate(overt_node_seq):
                if str(node) == str(value):
                    return ('DNode', 'overt', idx, j)

        # Check if it's the covert nodes.
        for idx, covert_node_seq in enumerate(df.enum_covert_node_seqs()):
            for j, node in enumerate(covert_node_seq):
                if str(node) == str(value):
                    return ('DNode', 'covert', idx, j)

    # Check if its a member of the phonological-form sort.
    if '_PFNode_' in str(value):
        return ('PFNode', df.pfInterface.get_pf(value)) 

    # Check if it's a member of the category sort.
    if str(value) in df.str2cat:
        return ('CatNode', str(value))
    elif str(value) == 'null':
        return ('CatNode', str(value))

    assert False, (type(value), str(value), value, repr(value))
    None


def enum_unary_funcs(derivation_formula):
    df = derivation_formula
    return {'head': df.head,
            'parent': df.parent,
            'cat_map': df.cat_map,
            'move_loc': df.move_loc,
            'head_movement': df.head_movement,
            'pf_map': df.pf_map}


"""
def enum_binary_funcs(derivation_formula):
    df = derivation_formula
    {'dominates': df.dominates,
     'nmdom': df.nmdom,
     'precedes': df.precedes}
"""

def serialize_model_values(derivation_model):
    dm = derivation_model
    df = dm.formula
    m_eval = dm.model.evaluate

    # Extract (derivation) model parameters.
    mv = {'params': {'max_num_feats': df.MAX_NUM_FEATURES_PER_LEXICAL_ENTRY,
                     'num_overt_lex_items': df.NUM_WORDS,
                     'num_covert_lex_items': df.MAX_NUM_EMPTY_LEXICAL_ITEMS,
                     'tokens': df.whitelisted_surface_forms[0]},
          'funcs': {}}

    # Extract values for unary functions.
    def serialize_unary_func(fn):
        print("function = " + str(fn))
        return [[serialize_value(node, dm) for node in  [x, m_eval(fn(x))]]
                for x in df.all_nodes()]

    for fn_label, fn in enum_unary_funcs(df).items():
        mv['funcs'][fn_label] = serialize_unary_func(fn)

    """
    # Extract values for binary functions.
    def serialize_binary_func(fn):
        return [[serialize_value(node, dm) for node in [x, y, m_eval(fn(x))]]
                for x, y in product(df.all_nodes(), df.all_nodes())]

    for fn_label, fn in enum_binary_funcs(df).items():
        mv['funcs'][fn_label] = serialize_binary_func(fn)
    """

    return copy.deepcopy(mv)


def deserialize_model_values(derivation_formula, model_values_mapping):
    """
    Load constraints.
    """    

    df = derivation_formula
    s = df.solver
    mv = model_values_mapping
    
    # Check that the model parameters agree with the parameters of the
    # derivation formula.

    # Enforce values for unary functions.
    def enforce_unary_func(fn, value_tuples):
        for x, y in value_tuples:
            x_value = deserialize_value(x, df)
            y_value = deserialize_value(y, df)
            s.add_singleton(fn(x_value) == y_value)

    for fn_label, fn in enum_unary_funcs(df).items():
        with s.group(tag="Enforcing the unary function: " + fn_label): 
            enforce_unary_func(fn, mv['funcs'][fn_label])

    """
    # Enforce values for binary functions.
    def enforce_binary_func(fn, value_tuples):
        for x, y in value_tuples:
            x_value = deserialize_value(x)
            y_value = deserialize_value(y)
            z_value = deserialize_value(y)
            s.add_singleton(fn(x_value, y_value) == z_value)
    
    for fn_label, fn in enum_binary_funcs(df).items():
        with s.group(tag="Enforcing the binary function: " + fn_label): 
            enforce_binary_func(fn, mv['funcs'][fn_label])
    """
