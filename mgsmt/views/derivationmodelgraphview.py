#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

from z3 import *

import mgsmt
from mgsmt.solver.solver_utils import distinct, ordered, same_node
from mgsmt.views.modeltableview import ModelTableView

from itertools import product

from IPython.core.display import display, HTML

class DerivationModelGraphView(ModelGraphView):

    def __init__(self, derivation_model, lexicon_model=None):
        self.dm = derivation_model

        # Construct the graphviz representation.

        self.gviz_repr = None
