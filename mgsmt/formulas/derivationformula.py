#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
An SMT formula encoding an MG derivation.
"""

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


class DerivationFormula(SMTFormula):

    CatSort = None

    def _init_cat_sort():
        if DerivationFormula.CatSort is None:
            sort = Datatype("%s_%s"%("category_sort_", "CatNode"))
            subtypes = ['C_declarative', 'C_question', 'T', 'v', 'V', 'P', 'D', 'N', 'null']
            for subtype in subtypes:
                sort.declare(subtype)
            DerivationFormula.CatSort = sort.create()

    #------------------------------------------------------------------------------#
    # Accessor functions for the hierarchy of derivation nodes.
    #------------------------------------------------------------------------------#
    def all_nodes(self):
        yield self.null_node
        yield from self.nodes()

    def nodes(self):
        yield from self.lex1nodes()
        yield from self.intermediate4nodes()
        yield self.root_node

    def lex1nodes(self):
        yield from self.overt2lex2nodes()
        yield from self.covert3lex3nodes()

    def overt2lex2nodes(self):
        yield from self.__overt_lexical_nodes__

    def covert3lex3nodes(self):
        yield from self.__covert_lexical_nodes__

    def intermediate4nodes(self):
        yield from self.__intermediate_nodes__

    def non6root6nodes(self):
        yield from self.lex1nodes()
        yield from self.intermediate4nodes()

    def all_non_lexical_nodes(self):
        yield self.null_node
        yield from self.intermediate4nodes()
        yield self.root_node

    def node_seqs(self):
        yield from self.__node_seqs__.values()

    def get_overt_node_seq(self, index):
        s_node = list(self.overt2lex2nodes())[index]
        return self.__node_seqs__[s_node]

    def enum_overt_node_seqs(self):
        for x in self.overt2lex2nodes():
            yield self.__node_seqs__[x]

    def enum_covert_node_seqs(self):
        for x in self.covert3lex3nodes():
            yield self.__node_seqs__[x]

    def get_surface_forms(self):
        assert len(self.whitelisted_surface_forms) == 1
        return list(self.whitelisted_surface_forms)[0]

    #------------------------------------------------------------------------------#
    # Methods for restricting the domain and range of uninterpreted functions.
    #------------------------------------------------------------------------------#
    def restrict_unary_func(self,
                            fn,
                            fn_domain,
                            fn_range=None,
                            bottom=None,
                            no_fixed_points=False,
                            only_active=True):
        assert fn.arity() == 1
        if bottom is None:
            bottom = self.null_node
        fn_domain = list(fn_domain)
        for x in fn_domain:
            if x is bottom:
                assert False
        s = self.solver
        with s.group('Domain Restriction for the (unary) function: ' + repr(fn)):
            s.add_conj(fn(x) == bottom for x in self.all_nodes() if x not in fn_domain)
        if fn_range:
            with s.group('Range Restriction for the (unary) function: ' + repr(fn)):
                fn_range = list(fn_range)
                s.add_conj(Or([fn(x) == y for y in fn_range]) for x in fn_domain)
        if no_fixed_points:
            with s.group('No-fixed-points property for the (unary) function: ' + repr(fn)):
                s.add_conj(fn(x) != x for x in fn_domain)

    def restrict_unary_only_active(self, fn):
        with self.solver.group(tag='Only active nodes may be mapped to non-null nodes.'):
            self.solver.add_conj(Implies(self.head(x) == self.null_node,
                                         fn(x) == self.null_node)
                                 for x in self.all_nodes())
            self.solver.add_conj(Implies(self.head(fn(x)) == self.null_node,
                                         fn(x) == self.null_node)
                                 for x in self.all_nodes())

    def restrict_binary_pred_only_active(self, pred):
        with self.solver.group(tag='Only active nodes may be mapped to non-null nodes.'):
            self.solver.add_conj(Implies(Or(self.head(x) == self.null_node,
                                            self.head(y) == self.null_node),
                                         Not(pred(x, y)))
                                 for x, y in product(self.all_nodes(), repeat=2))

    def restrict_binary_func(self,
                             fn,
                             arg1_domain,
                             arg2_domain,
                             fn_range=None,
                             bottom=None,
                             irreflexive=False,
                             symmetric=False,
                             anti_symmetric=False,
                             transitive=False):
        assert fn.arity() == 2
        arg1_domain, arg2_domain = list(arg1_domain), list(arg2_domain)
        if bottom is None:
            bottom = self.null_node
        for x in chain(arg1_domain, arg2_domain):
            if x is bottom:
                assert False
        with self.solver.group('Domain Restriction for the (binary) function: ' + repr(fn)):
            self.solver.add_conj(fn(x, y) == bottom
                                 for x, y in product(self.all_nodes(), repeat=2)
                                 if x not in arg1_domain or y not in arg2_domain)
        if fn_range:
            with self.solver.group('Range Restriction for the (binary) function: ' + repr(fn)):
                fn_range = list(fn_range)
                self.solver.add_conj(Or([fn(x, y) == z for z in fn_range])
                                     for x, y in product(arg1_domain, arg2_domain))
        if irreflexive:
            with self.solver.group('Irreflexive property for the (binary) function: ' + repr(fn)):
                self.solver.add_conj(fn(x, x) == bottom for x in self.all_nodes())
        if symmetric:
            with self.solver.group('Symmetric property for the (binary) function: ' + repr(fn)):
                self.solver.add_conj(fn(x, y) == fn(y, x)
                                     for x, y in product(self.all_nodes(), repeat=2))
        if anti_symmetric:
            with self.solver.group('Anti-symmetric property for the (binary) function: ' + repr(fn)):
                self.solver.add_conj(Implies(fn(x, y) != bottom, fn(y, x) == bottom)
                                     for x, y in distinct(product(self.all_nodes(), repeat=2)))
        if transitive:
            with self.solver.group('Transitive property for the (binary) function: ' + repr(fn)):
                self.solver.add_conj(Implies(And(fn(x, y) != bottom, fn(y, z) != bottom),
                                             fn(x, z) != bottom)
                                     for x, y, z in product(self.all_nodes(), repeat=3))

    #------------------------------------------------------------------------------#
    # Initialization.
    #------------------------------------------------------------------------------#
    def __init__(self,
                 solver,
                 pfInterface,
                 NUM_WORDS,
                 MAX_NUM_EMPTY_LEXICAL_ITEMS,
                 MAX_NUM_MOVEMENTS,
                 MAX_NUM_HEAD_MOVEMENTS,
                 MAX_NUM_FEATURES_PER_LEXICAL_ENTRY,
                 whitelisted_surface_forms,
                 lexicon_formula=None,
                 include_precedence_relations=True):
        super().__init__(solver)
        self.pfInterface = pfInterface
        self.include_precedence_relations = include_precedence_relations
        self.ic_dict = {'categorical': [], 'locality': [], 'sent_type': []}

        assert len(whitelisted_surface_forms) == 1
        assert 0 < len(whitelisted_surface_forms[0]) <= NUM_WORDS
        self.whitelisted_surface_forms = whitelisted_surface_forms
        
        self.NUM_WORDS = NUM_WORDS # i.e. overt lexical items
        self.MAX_NUM_EMPTY_LEXICAL_ITEMS = MAX_NUM_EMPTY_LEXICAL_ITEMS
        self.MAX_NUM_MOVEMENTS = MAX_NUM_MOVEMENTS
        self.MAX_NUM_HEAD_MOVEMENTS = MAX_NUM_HEAD_MOVEMENTS
        self.MAX_NUM_FEATURES_PER_LEXICAL_ENTRY = MAX_NUM_FEATURES_PER_LEXICAL_ENTRY

        assert 2 <= self.NUM_WORDS
        assert 0 <= self.MAX_NUM_MOVEMENTS
        assert 0 <= self.MAX_NUM_EMPTY_LEXICAL_ITEMS
        assert 2 <= MAX_NUM_FEATURES_PER_LEXICAL_ENTRY

        self.NUM_LEXICAL_NODES = NUM_WORDS + MAX_NUM_EMPTY_LEXICAL_ITEMS
        num_nodes = 2 + MAX_NUM_FEATURES_PER_LEXICAL_ENTRY * self.NUM_LEXICAL_NODES

        with self.solver.group(tag='Start'):
            pass

        self.__init_members__(num_nodes=num_nodes)

    def __init_members__(self, num_nodes):
        """
        Initialize Sorts, Enumerations, Functions, etc.
        """
        with self.solver.group(tag='Initializing Sorts'):
            self.NodeSort, d_nodes = self.create_finite_sort('DNode', num_nodes)
            self.null_node = null_node = d_nodes[0]
            self.root_node = root_node = d_nodes[-1]
            self.__overt_lexical_nodes__ = d_nodes[1:1+self.NUM_WORDS]
            self.__covert_lexical_nodes__ = set(d_nodes[1+self.NUM_WORDS:1+self.NUM_LEXICAL_NODES])
            self.__intermediate_nodes__ = set(d_nodes[1+self.NUM_LEXICAL_NODES:-1])

            # Categories
            DerivationFormula._init_cat_sort()
            self.CatSort = DerivationFormula.CatSort
            self.str2cat = {
                'C_declarative': self.CatSort.C_declarative,
                'C_question': self.CatSort.C_question,
                'T': self.CatSort.T,
                'v': self.CatSort.v,
                'V': self.CatSort.V,
                'P': self.CatSort.P,
                'D': self.CatSort.D,
                'N': self.CatSort.N}

        with self.solver.group(tag='Initializing (Uninterpreted) Functions'):
            # Model Functions
            self.parent = self.create_func('parent', self.NodeSort, self.NodeSort)
            self.merged = self.create_func('merged', self.NodeSort, self.NodeSort, self.NodeSort)
            self.dominates = self.create_func('dominates', self.NodeSort, self.NodeSort, BoolSort())
            self.move_loc = self.create_func('move_loc', self.NodeSort, self.NodeSort)
            self.nmdom = self.create_func('nmdom', self.NodeSort, self.NodeSort, BoolSort())
            self.pf_map = self.create_func('pf_map', self.NodeSort, self.pfInterface.PFNodeSort)
            self.head = self.create_func('head', self.NodeSort, self.NodeSort)
            self.precedes = self.create_func('precedes', self.NodeSort, self.NodeSort, BoolSort())
            self.head_movement = self.create_func('head_movement', self.NodeSort, self.NodeSort)
            self.cat_map = self.create_func('cat_map', self.NodeSort, self.CatSort)
            # Utility functions
            self.is_lexical = lambda x: And(self.head(x) == x, x != self.null_node)
            self.projects = lambda x: And(self.head(x) != self.null_node,
                                          x != self.root_node,
                                          self.head(x) == self.head(self.parent(x)))

        # Construct the node-sequences.
        tmp_nodes = set([x for x in self.intermediate4nodes()])
        self.__node_seqs__ = {}
        for x in self.lex1nodes():
            ns = [x]
            for i in range(1, self.MAX_NUM_FEATURES_PER_LEXICAL_ENTRY):
                ns.append(tmp_nodes.pop())
            self.__node_seqs__[x] = tuple(ns)

    def add_UG_constraints(self):
        """
        Add the axioms for a logical formulation of an MG derivation.
        """
        # For convenience/brevity.
        pfInterface = self.pfInterface
        null_node = self.null_node
        root_node = self.root_node
        parent = self.parent
        merged = self.merged
        dominates = self.dominates
        move_loc = self.move_loc
        head_movement = self.head_movement
        nmdom = self.nmdom
        pf_map = self.pf_map
        head = self.head
        precedes = self.precedes
        cat_map = self.cat_map
        cats = self.CatSort
        s = self.solver

        #------------------------------------------------------------------------------#
        # Node Sequence Framework
        #------------------------------------------------------------------------------#
        with s.group(tag='Node Sequence Framework'):
            # Introduce concept of node-seqs. (start_node, tail_nodes)
            with s.group(tag='Domination and Non-Moving Domination'):
                s.add_conj(And(Not(dominates(x, y)), Not(nmdom(x, y)))
                           for ns in self.node_seqs()
                           for ((i, x), (j, y)) in distinct(product(enumerate(ns), repeat=2))
                           if i <= j)
            with s.group(tag='Parent'):
                s.add_conj(parent(x) != y
                           for ns in self.node_seqs()
                           for ((i, x), (j, y)) in distinct(product(enumerate(ns), repeat=2))
                           if j != i + 1)
            with s.group(tag='Move-Location'):
                s.add_conj(Or(move_loc(x) == ns[i+1], move_loc(x) == null_node)
                           for ns in self.node_seqs()
                           for (i, x) in enumerate(ns[:-1]))
            with s.group(tag='Merged'):
                with s.group('Endocentricity(?): A node cannot merge with another node within the same projection.'):
                    s.add_conj(merged(x, y) == null_node
                               for ns in self.node_seqs()
                               for x, y in distinct(product(ns, ns)))
                with s.group():
                    for ns_a, ns_b in distinct(product(self.node_seqs(), repeat=2)):
                        for (i, a) in enumerate(ns_a):
                            for (j, b) in enumerate(ns_b):
                                zz = [null_node, root_node]
                                if i < len(ns_a)-1:
                                    zz.append(ns_a[i+1])
                                if j < len(ns_b)-1:
                                    zz.append(ns_b[j+1])
                                s.add(Or([merged(a, b) == z for z in zz]))
            with s.group(tag='Prohibition on Merges Criss-Crossing'):
                s.add_conj(Or(merged(a1, b2) == null_node, merged(b1, a2) == null_node)
                           for ns_a, ns_b in distinct(product(self.node_seqs(), repeat=2))
                           for (i1, a1), (i2, a2) in distinct(product(enumerate(ns_a), repeat=2))
                           for (j1, b1), (j2, b2) in distinct(product(enumerate(ns_b), repeat=2))
                           if (i1 < i2) and (j1 < j2))
            with s.group(tag='Head'):
                s.add_conj(Or(head(x) == head(ns[0]), head(x) == null_node)
                           for ns in self.node_seqs()
                           for x in ns)
                s.add_conj(Implies(head(x) == null_node,
                                   And([head(y) == null_node for y in ns[i+1:]]))
                           for ns in self.node_seqs()
                           for (i, x) in enumerate(ns[:-1]))
            with s.group(tag='Succession'):
                s.add_conj(Or(parent(x) == ns[i+1],
                              move_loc(x) == ns[i+1],
                              head(ns[i+1]) == null_node)
                           for ns in self.node_seqs()
                           for (i, x) in enumerate(ns[:-1]))
            with s.group():
                s.add_conj(move_loc(ns[-1]) == null_node for ns in self.node_seqs())

        #------------------------------------------------------------------------------#
        # Parent Relations
        #------------------------------------------------------------------------------#
        with s.group(tag='Parent Relations'):
            self.restrict_unary_func(fn=parent,
                                     fn_domain=self.non6root6nodes(),
                                     fn_range=self.all_non_lexical_nodes(),
                                     no_fixed_points=True)
            self.restrict_unary_only_active(parent)
            with s.group(tag='Intermediate nodes with children have a non-null parent'):
                s.add_conj(Implies(Distinct(null_node, parent(x), root_node),
                                   parent(parent(x)) != null_node)
                           for x in self.non6root6nodes())
            with s.group(tag='Every parent has exactly two children'):
                s.add_conj(Implies(parent(x) != null_node,
                                   PbEq([(parent(x) == parent(y), 1)
                                         for y in self.non6root6nodes()],
                                        k=2))
                           for x in self.non6root6nodes())

        #------------------------------------------------------------------------------#
        # Head Relations
        #------------------------------------------------------------------------------#
        with s.group(tag='Head Relations'):
            self.restrict_unary_func(fn=head,
                                     fn_domain=self.nodes(),
                                     fn_range=chain([self.null_node], self.lex1nodes()))
            self.restrict_unary_only_active(head)
            s.add_conj(Xor(head(x) == null_node, head(x) == x) for x in self.lex1nodes())
            s.add_conj(Implies(head(x) != null_node, parent(x) != null_node)
                       for x in self.non6root6nodes())

        #------------------------------------------------------------------------------#
        # Categories and Extended Projections
        #------------------------------------------------------------------------------#
        with s.group(tag='Categories and Extended Projections'):
            s.add_conj((cat_map(x) == cats.null) == (head(x) == null_node)
                       for x in self.all_nodes())
            s.add_conj(cat_map(x) == cat_map(head(x))
                       for x in self.all_nodes())
            s.add(Or([cat_map(root_node) == cats.C_declarative,
                      cat_map(root_node) == cats.C_question]))

            def is_comp(x, y):
                return And(merged(x, y) != null_node, head(parent(x)) == head(x))

            def proj_hier(catA, catB):
                # catA dominates catB
                s.add_conj(Implies(And(is_comp(x, y), cat_map(x) == catA),
                                   cat_map(y) == catB)
                           for x, y in distinct(product(self.lex1nodes(),
                                                        self.all_nodes())))

            with s.group(tag='Clausal Extended Projection'):
                proj_hier(cats.C_declarative, cats.T)
                proj_hier(cats.C_question, cats.T)
                proj_hier(cats.T, cats.v)
                proj_hier(cats.v, cats.V)

            with s.group(tag='Nominal Extended Projection'):
                proj_hier(cats.P, cats.D)
                proj_hier(cats.D, cats.N)

            with s.group(tag='Categories C, T, v and P must have a complement.'):
                comp_cats = (cats.C_declarative, cats.C_question, cats.T, cats.v, cats.P)
                s.add_conj(Implies(cat_map(x) == cat, head(parent(x)) == head(x))
                           for x in self.lex1nodes()
                           for cat in comp_cats)

            with s.group(tag='Nouns do not project.'):
                s.add_conj(Implies(cat_map(x) == cats.N, head(parent(x)) != x)
                           for x in self.lex1nodes())

            with s.group(tag="Lex. heads of merged structs. have distinct categories."):
                s.add_conj(Implies(cat_map(x) == cat_map(y), merged(x, y) == null_node)
                           for x, y in distinct(product(self.all_nodes(), repeat=2)))

        #------------------------------------------------------------------------------#
        # Domination Relations -- i.e. "X dominates Y"
        #------------------------------------------------------------------------------#
        with s.group(tag='Domination Relations'):
            self.restrict_binary_func(fn=dominates,
                                      arg1_domain=chain(self.intermediate4nodes(),
                                                        [root_node]),
                                      arg2_domain=self.non6root6nodes(),
                                      bottom=False,
                                      irreflexive=True,
                                      anti_symmetric=True,
                                      transitive=True)
            self.restrict_binary_pred_only_active(dominates)
            with s.group('Implications of dominance'):
                s.add_conj(Implies(dominates(x, y),
                                   Xor(x == parent(y), dominates(x, parent(y))))
                           for x, y in distinct(product(self.nodes(), self.nodes())))
                with s.group(tag='Parenthood implies dominance'):
                    s.add_conj(Implies(parent(x) != null_node, dominates(parent(x), x))
                               for x in self.all_nodes())

        #------------------------------------------------------------------------------#
        # Merge Relations
        #------------------------------------------------------------------------------#
        with s.group(tag='Merge Relations'):
            self.restrict_binary_func(fn=merged,
                                      arg1_domain=self.non6root6nodes(),
                                      arg2_domain=self.non6root6nodes(),
                                      fn_range=self.all_non_lexical_nodes(),
                                      irreflexive=True,
                                      symmetric=True)
            with s.group(tag='Both arguments to merge have the same parents.'):
                s.add_conj(merged(x, y) == If(parent(x) == parent(y), parent(x), null_node)
                           for x, y in distinct(product(self.all_nodes(), self.all_nodes())))
            with s.group(tag='Exactly one argument to merge projects.'):
                s.add_conj(Implies(parent(x) == parent(y),
                                   Or(head(parent(x)) == head(x), head(parent(y)) == head(y)))
                           for x, y in distinct(product(self.non6root6nodes(), repeat=2)))
            with s.group(tag='UTAH Related Conditions'):
                s.add_conj(Not(And(Distinct(null_node, head(x), head(y), head(parent(x))),
                                   head(x) == head(y),
                                   head(parent(x)) == head(parent((y)))))
                           for x, y in distinct(product(self.nodes(), repeat=2)))

        #------------------------------------------------------------------------------#
        # Move Relations
        #------------------------------------------------------------------------------#
        with s.group(tag='Movement Relations'):
            self.restrict_unary_func(fn=move_loc,
                                     fn_domain=self.non6root6nodes(),
                                     fn_range=chain([null_node],
                                                    self.intermediate4nodes()),
                                     no_fixed_points=True)
            self.restrict_unary_only_active(move_loc)
            with s.group(tag="Projection along movement chain."):
                s.add_conj(Implies(move_loc(x) == y,
                                   And(head(x) != head(parent(x)),
                                       head(y) != head(parent(y))))
                           for x, y in distinct(product(self.nodes(),
                                                        self.intermediate4nodes())))
            with s.group(tag='Maximum number of movements'):
                s.add_conj([PbLe([(move_loc(x) != null_node, 1)
                                  for x in self.all_nodes()],
                            k=self.MAX_NUM_MOVEMENTS)])
            with s.group(tag="Parent of movement-target must dominate parent of movement-source"):
                s.add_conj(Implies(move_loc(x) == y,
                                   dominates(parent(y), parent(x)))
                           for x, y in distinct(product(self.non6root6nodes(),
                                                        self.intermediate4nodes())))

        #------------------------------------------------------------------------------#
        # Head-Movement Relations.
        #------------------------------------------------------------------------------#
        with s.group(tag='Head Movement Relations'):
            self.restrict_unary_func(fn=head_movement,
                                     fn_domain=self.lex1nodes(),
                                     fn_range=chain([null_node], self.lex1nodes()),
                                     no_fixed_points=True)
            self.restrict_unary_only_active(head_movement)
            s.add_conj(Implies(head_movement(x) == y,
                               And(head(parent(y)) == y,
                                   move_loc(x) == null_node,
                                   dominates(parent(y), x)))
                       for x, y in distinct(product(self.lex1nodes(), repeat=2)))
            s.add_conj(Implies(And(head_movement(x) == y,
                                   merged(y, z) != null_node),
                               head(z) == x)
                       for x, y, z in distinct(product(self.lex1nodes(),
                                                       self.lex1nodes(),
                                                       self.intermediate4nodes())))
            with s.group(tag='Maximum number of head-movement operations.'):
                s.add_conj([PbLe([(head_movement(x) != null_node, 1)
                                  for x in self.lex1nodes()],
                                 k=self.MAX_NUM_HEAD_MOVEMENTS)])
            with s.group(tag='Head-movement restricts further head movement'):
                s.add_conj(Implies(head_movement(x) == y,
                                   head_movement(y) == null_node)
                           for x, y in distinct(product(self.lex1nodes(), repeat=2)))

        #------------------------------------------------------------------------------#
        # Non-Move Domination Relations (used for computing precedence).
        #------------------------------------------------------------------------------#
        with s.group(tag='Non-moving Domination Relations'):
            self.restrict_binary_func(fn=nmdom,
                                      arg1_domain=chain(self.intermediate4nodes(),
                                                        [root_node]),
                                      arg2_domain=self.non6root6nodes(),
                                      bottom=False,
                                      irreflexive=True,
                                      anti_symmetric=True,
                                      transitive=True)
            self.restrict_binary_pred_only_active(nmdom)
            with s.group(tag='Every node is nmdom by either parent or move location'):
                s.add_conj(Implies(parent(x) != null_node,
                                   Xor(nmdom(parent(x), x), nmdom(move_loc(x), x)))
                           for x in self.all_nodes())
                s.add_conj(Implies(move_loc(x) != null_node,
                                   nmdom(move_loc(x), x))
                           for x in self.all_nodes())

        #------------------------------------------------------------------------------#
        # Precedence Relations
        #------------------------------------------------------------------------------#
        with s.group(tag='Precedence Relations'):
            self.restrict_binary_func(fn=precedes,
                                      arg1_domain=self.lex1nodes(),
                                      arg2_domain=self.lex1nodes(),
                                      bottom=False,
                                      irreflexive=True,
                                      anti_symmetric=True)
            self.restrict_binary_pred_only_active(precedes)
            if not self.include_precedence_relations:
                s.log_msg("DFormula: constraints precedence relations were not included.")
            else:
                s.log_msg("DFormula: constraints precedence relations were included.")
                s.add_conj(precedes(x, y) == (i < j)
                           for ((i, x), (j, y)) in product(enumerate(self.overt2lex2nodes()),
                                                           repeat=2))
                s.add_conj(Implies(And(merged(x, y) != null_node,
                                       head(x) == head(parent(x)),
                                       move_loc(y) == null_node,
                                       head_movement(head(x)) == null_node,
                                       head_movement(head(y)) == null_node),
                                   If(self.is_lexical(x),
                                      precedes(head(x), head(y)),
                                      precedes(head(y), head(x))))
                           for x, y in distinct(product(self.non6root6nodes(), repeat=2)))
                s.add_conj(Implies(And(nmdom(x, y),
                                       nmdom(y, z),
                                       Distinct(head(x), head(y), head(z), null_node),
                                       head_movement(head(x)) == null_node,
                                       head_movement(head(y)) == null_node,
                                       head_movement(head(z)) == null_node),
                                   And(precedes(head(x), head(y)) == precedes(head(x), head(z)),
                                       precedes(head(y), head(x)) == precedes(head(z), head(x))))
                           for x, y, z in distinct(product(self.nodes(),
                                                           self.intermediate4nodes(),
                                                           self.non6root6nodes())))
                s.add_conj(Implies(And(Distinct(x, y, parent(x), null_node),
                                       Distinct(head(x), head(y), null_node),
                                       Distinct(head(parent(x)), head(y), null_node),
                                       nmdom(parent(x), y),
                                       nmdom(parent(x), x),
                                       Not(dominates(x, y)),
                                       Not(dominates(y, x)),
                                       parent(x) != parent(y),
                                       head_movement(head(y)) == null_node),
                                    precedes(head(x), head(y)))
                           for x, y in distinct(product(self.non6root6nodes(), repeat=2)))
                s.add_conj(Implies(And(Distinct(x, y, x_desc, parent(x), null_node),
                                       Distinct(head(x), head(y), null_node),
                                       Distinct(head(parent(x)), head(y), null_node),
                                       Distinct(head(x_desc), head(y), null_node),
                                       nmdom(parent(x), y),
                                       nmdom(parent(x), x),
                                       nmdom(x, x_desc),
                                       Not(dominates(x, y)),
                                       Not(dominates(y, x)),
                                       parent(x) != parent(y),
                                       head_movement(head(y)) == null_node,
                                       head_movement(head(x)) == null_node),
                                   precedes(head(x_desc), head(y)))
                           for x_desc, x, y in distinct(product(self.non6root6nodes(),
                                                                repeat=3)))
                s.add_conj(Implies(head_movement(x) == y, precedes(x, y))
                           for x, y in distinct(product(self.lex1nodes(), repeat=2)))
                s.add_conj(Implies(head_movement(x) == y,
                                   And(Not(And(precedes(x, z), precedes(z, y))),
                                       Not(And(precedes(y, z), precedes(z, x)))))
                           for x, y, z in distinct(product(self.lex1nodes(), repeat=3)))

        #------------------------------------------------------------------------------#
        # PF-Interface Relations
        #------------------------------------------------------------------------------#
        with s.group(tag='PF-Interface Relations'):
            self.restrict_unary_func(fn=pf_map,
                                     fn_domain=self.lex1nodes(),
                                     bottom=pfInterface.null_pf_node)
            with s.group(tag='Overt start nodes can never be covert PFs'):
                s.add_conj(pfInterface.pf_node_type(pf_map(x)) != pfInterface.PFTypeSort.Covert
                           for x in self.overt2lex2nodes())
            with s.group(tag='Covert start nodes can never be overt PFs'):
                s.add_conj(pfInterface.pf_node_type(pf_map(x)) != pfInterface.PFTypeSort.Overt
                           for x in self.covert3lex3nodes())
            with s.group(tag='A start node that maps to the null PF must be Inactive'):
                s.validate_conj(Implies(pfInterface.pf_node_type(pf_map(x)) == pfInterface.PFTypeSort.Null,
                                        head(x) == null_node)
                                for x in self.lex1nodes())

        #------------------------------------------------------------------------------#
        # Interface Conditions
        #------------------------------------------------------------------------------#
        with s.group(tag='Interface Conditions'):
            #s.validate_conj(head(x) != null_node for x in self.overt2lex2nodes())
            s.add_conj(head(x) != null_node for x in self.overt2lex2nodes())
            assert len(self.whitelisted_surface_forms) == 1

            with s.group(tag='White-listed Surface Forms'):
                idx2pfnode = lambda i: list(self.overt2lex2nodes())[i]
                sentence = self.whitelisted_surface_forms[0]
                s.add_conj([pf_map(idx2pfnode(i)) == pfInterface.get_pf_node(word)
                            for i, word in enumerate(sentence)])


        with s.group(tag='End'):
            pass

    #-------------------------------------------------------------------------#
    # Constraints for Interface Conditions
    #-------------------------------------------------------------------------#
    def add_ic_constraints(self,
                           locality_constraints=None,
                           sent_type_constraint=None,
                           categorical_constraints=None,
                           tokens=None):
        s = self.solver
        # Add constraints from interface conditions.
        if sent_type_constraint:
            result = self.add_sent_type_constraint(sent_type_constraint)
            self.ic_dict['sent_type'] = sent_type_constraint
        if categorical_constraints:
            result = self.add_categorical_constraints(categorical_constraints)
            self.ic_dict['categorical_constraints'] = {k:[x[0] for x in v]
                                                       for k, v in categorical_constraints.items()}
        if tokens:
            with s.group(tag='White-listed Surface Forms'):
                idx2pfnode = lambda i: self.pf_map(list(self.overt2lex2nodes())[i])
                s.add_conj([idx2pfnode(i) == self.pfInterface.get_pf_node(word)
                            for i, word in enumerate(tokens)])
        if locality_constraints:
            for lc_type, lc_args in locality_constraints:
                if lc_type == "theta":
                    result = self.add_arg_struct_constraints(**lc_args)
                    self.ic_dict['locality'].append((lc_type, lc_args, result))
                elif lc_type == "agree":
                    result = self.add_agreement_constraint(**lc_args)
                    self.ic_dict['locality'].append((lc_type, lc_args, result))
                else:
                    assert False, f"Unrecognized locality constraint type: {lc_type!r}"

    def arg_phrase_nodes(self, idxs):
        return [ns[0]
                for i, ns in enumerate(self.enum_overt_node_seqs())
                if i in idxs]

    def is_dom_arg_phrase(self, x, ys):
        a = And([Or(x == y, Or([self.dominates(x, y), self.nmdom(x, y)]))
                 for y in ys])
        b = Or([self.head(x) == y for y in ys])
        return And(a, b)

    def is_arg_cat(self, x):
        cs = self.CatSort
        arg_cats = (cs.P, cs.D, cs.N, cs.C_declarative, cs.C_question)
        return Or([self.cat_map(x) == c for c in arg_cats])

    def validate_pred_arg_words(self, pred, arg):
        # Validate words listed in the predicate and argument are *overt* forms
        # registered with the PFInterface.
        for w, _ in pred:
            assert w in self.pfInterface.overt_forms,\
              "%r not in %r"%(w, self.pfInterface.overt_forms)

        for w, _ in arg:
            assert w in self.pfInterface.overt_forms,\
              "%r not in %r"%(w, self.pfInterface.overt_forms)

    def pred_arg_subj_constraint(self, pred, arg, negation_mode=False):
        assert pred and arg
        self.validate_pred_arg_words(pred, arg)
        p_idxs = [i for (w, i) in pred]
        assert len(p_idxs) == 1
        a_idxs = [i for (w, i) in arg]
        arg_nodes = self.arg_phrase_nodes(a_idxs)
        liable_pforms = [w for (w, _) in chain(pred, arg)]
        # Covert pform may be liable due to possibility of covert little-v.
        liable_pforms.append(self.pfInterface.EPSILON)
        probe = Const(f"probe_nodesort_{uuid.uuid4().int}", self.NodeSort)

        def subj_term(p_node, s_node, little_v_ns):
            probe_term = [] if negation_mode else [probe == little_v_ns[2]] 
            return And([self.cat_map(little_v_ns[0]) == self.CatSort.v,
                        self.cat_map(p_node) == self.CatSort.V,
                        self.is_arg_cat(s_node),
                        self.is_dom_arg_phrase(s_node, arg_nodes),
                        self.merged(little_v_ns[0], p_node) == little_v_ns[1],
                        self.merged(little_v_ns[1], s_node) == little_v_ns[2]] +
                       probe_term)

        term = Or([subj_term(p_node, a_node, little_v_ns)
                   for a_i, p_i in distinct(product(a_idxs, p_idxs))
                   for a_node in self.get_overt_node_seq(a_i)
                   for p_node in self.get_overt_node_seq(p_i)
                   for little_v_ns in self.enum_covert_node_seqs()])

        return {'term': term,
                'liable_pforms': liable_pforms,
                'probe': probe,
                'desc': 'predicate-subject-constraint'}

    def pred_arg_obj_constraint(self, pred, arg, negation_mode=False):
        assert pred and arg
        self.validate_pred_arg_words(pred, arg)
        p_idxs = [i for (w, i) in pred]
        assert len(p_idxs) == 1
        a_idxs = [i for (w, i) in arg]
        arg_nodes = self.arg_phrase_nodes(a_idxs)
        liable_pforms = [w for (w, _) in chain(pred, arg)]
        probe = Const(f"probe_nodesort_{uuid.uuid4().int}", self.NodeSort)
        
        def obj_term(p_node, o_node):
            probe_term = [] if negation_mode else [probe == self.merged(p_node, o_node)]
            return And([self.merged(p_node, o_node) != self.null_node,
                        self.head(self.parent(p_node)) == self.head(p_node),
                        self.cat_map(p_node) == self.CatSort.V,
                        self.is_arg_cat(o_node),
                        self.is_dom_arg_phrase(o_node, arg_nodes)] +
                       probe_term)

        term = Or([obj_term(p_node, a_node)
                   for p_i, a_i in distinct(product(p_idxs, a_idxs))
                   for a_node in self.get_overt_node_seq(a_i)
                   for p_node in self.get_overt_node_seq(p_i)[:2]])

        return {'term': term,
                'liable_pforms': liable_pforms,
                'probe': probe,
                'desc': 'predicate-obj-constraint'}

    def pred_arg_iobj_constraint(self, pred, arg, negation_mode=False):
        assert pred and arg
        self.validate_pred_arg_words(pred, arg)
        p_idxs = [i for (w, i) in pred]
        assert len(p_idxs) == 1
        a_idxs = [i for (w, i) in arg]
        arg_nodes = self.arg_phrase_nodes(a_idxs)
        liable_pforms = [w for (w, _) in chain(pred, arg)]
        # Covert pform may be liable due to possibility of null complementizer.
        liable_pforms.append(self.pfInterface.EPSILON)
        probe = Const(f"probe_nodesort_{uuid.uuid4().int}", self.NodeSort)
        
        def iobj_term(p_node, iobj_node):
            probe_term = [] if negation_mode else [probe == self.merged(p_node, iobj_node)]
            return And([self.merged(p_node, iobj_node) != self.null_node,
                        self.head(self.parent(p_node)) == self.head(p_node),
                        self.cat_map(p_node) == self.CatSort.V,
                        self.is_arg_cat(iobj_node),
                        Implies(self.cat_map(iobj_node) != self.CatSort.P,
                                self.cat_map(self.parent(self.parent(p_node))) != self.cat_map(self.parent(p_node))),
                        self.is_dom_arg_phrase(iobj_node, arg_nodes)] +
                       probe_term)

        overt_term = Or([iobj_term(p_node, a_node)
                         for p_i, a_i in distinct(product(p_idxs, a_idxs))
                         for a_node in self.get_overt_node_seq(a_i)
                         for p_node in self.get_overt_node_seq(p_i)[:2]])
        covert_term = Or([iobj_term(p_node, a_node)
                          for a_ns in self.enum_covert_node_seqs()
                          for p_i in p_idxs
                          for a_node in a_ns
                          for p_node in self.get_overt_node_seq(p_i)[:2]])
        term = Or(overt_term, covert_term)

        return {'term': term,
                'liable_pforms': liable_pforms,
                'probe': probe,
                'desc': 'predicate-iobj-constraint'}

    def agreement_constraint(self, pred, subj, negation_mode=False):
        p_idxs = [i for (w, i) in pred]
        assert len(p_idxs) == 1
        self.validate_pred_arg_words(pred, subj)
        s_idxs = [i for (w, i) in subj]
        liable_pforms = [w for (w, _) in chain(pred, subj)]
        probe = Const(f"probe_nodesort_{uuid.uuid4().int}", self.NodeSort)
        
        def agree_term(p_node, s_node):
            probe_term = [] if negation_mode else [probe == self.merged(s_node, p_node)] 
            return And([self.merged(s_node, p_node) != self.null_node,
                        self.is_dom_arg_phrase(s_node, self.arg_phrase_nodes(s_idxs)),
                        self.head(self.parent(p_node)) == self.head(p_node)] +
                       probe_term)

        term = Or([agree_term(p_node, s_node)
                   for s_i, p_i in distinct(product(s_idxs, p_idxs))
                   for s_node in self.get_overt_node_seq(s_i)
                   for p_node in self.get_overt_node_seq(p_i)])

        return {'term': term,
                'liable_pforms': liable_pforms,
                'probe': probe,
                'desc': 'agreement-constraint'}

    def sent_type_constraint(self, sent_type):
        if sent_type == 'declarative':
            root_cat_term = self.cat_map(self.root_node) == self.CatSort.C_declarative
        elif sent_type == 'question':
            root_cat_term = self.cat_map(self.root_node) == self.CatSort.C_question

        covert_node = list(self.enum_covert_node_seqs())[0][0]
        pf_eps_node = self.pfInterface.get_pf_node(self.pfInterface.EPSILON)
        n = len(self.__node_seqs__[covert_node])

        def sss(m):
            assert m > 0
            cn_ns = self.__node_seqs__[covert_node]
            if m == 1:
                return And([self.parent(cn_ns[0]) == self.root_node] +
                           [self.parent(cn_ns[i]) == self.null_node
                            for i in range(1, n)])
            elif m == 2:
                return And([self.parent(cn_ns[0]) == cn_ns[1],
                                self.parent(cn_ns[1]) == self.root_node] +
                               [self.parent(cn_ns[i]) == self.null_node
                                for i in range(2, n)])
            else:
                return And([self.parent(cn_ns[0]) == cn_ns[1]] +
                               [self.parent(cn_ns[i]) == cn_ns[i+1]
                                for i in range(1, m-1)] +
                               [self.parent(cn_ns[m-1]) == self.root_node] +
                               [self.parent(cn_ns[i]) == self.null_node
                                for i in range(m-1, n)])

        term = And(self.head(self.root_node) == covert_node,
                   self.head(covert_node) == covert_node,
                   self.pf_map(covert_node) == pf_eps_node,
                   Or([sss(m) for m in range(1, n)]),
                   root_cat_term)

        return {'term': term,
                'liable_pforms': [self.pfInterface.EPSILON],
                'desc': 'sentence-type-constraint'}

    def add_categorical_constraints(self, category_constraints):
        # TODO: Need to refactor this method so that exactly one
        # word's category constraint is enforced at a time.
        for str_category in category_constraints:
            for word, idx in category_constraints[str_category]:
                tag = f"Categorical constraints for word={word!r}, pos={idx!r}, cat={str_category!r}."
                with self.solver.group(tag=tag):
                    w_category = self.str2cat[str_category]
                    w_node = self.get_overt_node_seq(idx)[0]
                    term = self.cat_map(w_node) == w_category
                    self.solver.add_singleton(term)

    def add_arg_struct_constraints(self, pred=None, subj=None, obj=None, iobj=None):
        s = self.solver
        with s.group(tag="Argument Structure Constraints"):
            constraints = {}
            if subj:
                constraints['subj'] = self.pred_arg_subj_constraint(pred, subj)
                s.add_singleton(constraints['subj']['term'])
            if obj:
                constraints['obj'] = self.pred_arg_obj_constraint(pred, obj)
                s.add_singleton(constraints['obj']['term'])
            if iobj:
                constraints['iobj'] = self.pred_arg_iobj_constraint(pred, iobj)
                s.add_singleton(constraints['iobj']['term'])
            return constraints

    def add_agreement_constraint(self, pred, subj):
        with self.solver.group(tag="Agreement Constraints"):
            constraint = self.agreement_constraint(pred, subj)
            self.solver.add_singleton(constraint['term'])
            return constraint

    def add_sent_type_constraint(self, sent_type):
        if sent_type:
            assert isinstance(sent_type, str)
            assert sent_type in ('declarative', 'question')
            # This constraint asserts that the head(node) is the head of the
            # entire derivation.
            with self.solver.group(tag="Structural Constraints: Head of Root"):
                self.solver.add(self.sent_type_constraint(sent_type)['term'])

    def enum_ic_probes(self):
        for (lc_type, lc_args, constraint_data) in self.ic_dict['locality']:
            if lc_type == 'theta':
                for arg_label in constraint_data:
                    probe = constraint_data[arg_label]['probe']
                    ic = {'lc_type': lc_type, 'lc_args': lc_args, 'arg_label': arg_label}
                    yield copy.deepcopy((probe, ic))
            elif lc_type == 'agree':
                probe = constraint_data['probe']
                ic = {'lc_type': lc_type, 'lc_args': lc_args}
                yield copy.deepcopy((probe, ic))


    def add_negative_locality_constraints(self, locality_constraints, arg_label):
        s = self.solver
        if not arg_label:
            for lc in locality_constraints:
                if lc[0] == 'agree':
                    with s.group(tag="Enforcing negative locality constraint for agreement."):
                        pred = lc[1]['pred']
                        subj = lc[1]['subj']
                        term = self.agreement_constraint(pred, subj, negation_mode=True)['term']
                        s.add_singleton(Not(term))
                        return
        else:
            for lc in locality_constraints:
                if lc[0] == 'theta':
                    assert arg_label in lc[1]
                    with s.group(tag=f"Enforcing negative locality constraint for theta: {arg_label}."):
                        pred = lc[1]['pred']
                        arg = lc[1][arg_label]
                        print(f"Proc. Neg. Loc. Constraint. pred: {pred}; arg: {arg}.")
                        if arg_label == 'subj':
                            term = self.pred_arg_subj_constraint(pred, arg, negation_mode=True)['term']
                            s.add_singleton(Not(term))
                            return
                        elif arg_label == 'obj':
                            term = self.pred_arg_obj_constraint(pred, arg, negation_mode=True)['term']
                            s.add_singleton(Not(term))
                            return
                        elif arg_label == 'iobj':
                            term = self.pred_arg_iobj_constraint(pred, arg, negation_mode=True)['term']
                            s.add_singleton(Not(term))
                            return
