#!/usr/bin/env python3
# -*- coding: utf-8 -*-


__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from z3 import *

import mgsmt
from mgsmt.solver.solver_utils import distinct, ordered, same_node
from itertools import product

import tabulate

from IPython.core.display import display, HTML

class ModelGraphView:

    def __init__(self):
        pass

    def serialize(self, filepath):
        assert any([filepath.endswith(x)
                    for x in ('.pdf', '.svg', '.png')])
        assert False, "Not Yet Implemented."
        
