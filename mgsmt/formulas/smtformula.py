#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Base class used for constructing an SMT Formula (using Z3).
"""

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import itertools
from z3 import *
import mgsmt.solver.smtsolver

class SMTFormula(object):


    __next_unique_id__ = itertools.count()


    def __init__(self, solver):
        assert isinstance(solver, mgsmt.solver.smtsolver.SMTSolver)
        self.solver = solver
        self.formula_name = "%d"%(SMTFormula.__next_unique_id__.__next__())
        self.model = None


    def create_func(self, fn_name, *args):
        return Function(*(["%s_%s"%(self.formula_name, fn_name)] + list(args)))


    def create_finite_sort(self, sort_name, num_sorts):
        return EnumSort("SORT_%s_%s"%(self.formula_name, sort_name),
                        ['%s_%s_%d'%(self.formula_name, sort_name, i)
                         for i in range(num_sorts)])


    def create_datatype(self, datatype_name, subtypes):
        sort = Datatype("%s_%s"%(self.formula_name, datatype_name))
        for subtype in subtypes:
            sort.declare(subtype)
        return sort.create()
