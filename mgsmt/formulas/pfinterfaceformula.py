#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
An SMT formula encoding Phonological Forms and the PF Interface.
"""

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from mgsmt.formulas.smtformula import SMTFormula

class PFInterfaceFormula(SMTFormula):

    EPSILON = 'ε'

    def __init__(self, solver, overt_forms, covert_forms, null_pf_str="∅"):
        super().__init__(solver)

        assert isinstance(overt_forms, set)
        assert isinstance(covert_forms, set)
        if overt_forms.intersection(covert_forms):
            raise Exception("Overlap between %r and %r."%(overt_forms, covert_forms))

        self.overt_forms = list(overt_forms)
        self.covert_forms = list(covert_forms)
        self.phonetic_forms = self.overt_forms + self.covert_forms + [null_pf_str]

        self.PFNodeSort, self.pf_nodes = self.create_finite_sort('PFNode', len(self.phonetic_forms))
        self.overt_pf_nodes = self.pf_nodes[:len(self.overt_forms)]
        self.covert_pf_nodes = self.pf_nodes[len(self.overt_forms):-1]
        self.null_pf_node = self.pf_nodes[-1]

        self.PFTypeSort = self.create_datatype('PFNodeType', ['Covert', 'Overt', 'Null'])
        self.pf_node_type = self.create_func('pf_node_type', self.PFNodeSort, self.PFTypeSort)

        s = self.solver
        with s.group(tag='PFNodeType Relations'):
            s.add_conj(self.pf_node_type(node) == self.PFTypeSort.Overt
                       for node in self.overt_pf_nodes)
            s.add_conj(self.pf_node_type(node) == self.PFTypeSort.Covert
                       for node in self.covert_pf_nodes)
            s.add_singleton(self.pf_node_type(self.null_pf_node) == self.PFTypeSort.Null)

    def get_pf(self, pf_node):
        for pf, nd in zip(self.phonetic_forms, self.pf_nodes):
            if str(pf_node) == str(nd):
                return pf
        raise Exception("%r not in %r"%(pf_node, self.pf_nodes))

    def get_pf_node(self, pf_str):
        for pf, pf_node in zip(self.phonetic_forms, self.pf_nodes):
            if pf_str == pf:
                return pf_node
        raise Exception("%r not in %r"%(pf_str, self.phonetic_forms))

    def non_null_nodes(self):
        return self.overt_pf_nodes + self.covert_pf_nodes
