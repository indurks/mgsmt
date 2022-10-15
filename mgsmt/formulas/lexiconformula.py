#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import itertools, simplejson as json, pprint as pp
from itertools import product

import z3
from z3 import And, Or, Not, Implies, Xor, Distinct, If, PbEq, PbGe, PbLe
from z3 import BoolSort

import mgsmt
import mgsmt.formulas.smtformula
from mgsmt.formulas.smtformula import SMTFormula
import mgsmt.formulas.derivationformula
import mgsmt.solver.solver_utils
from mgsmt.solver.solver_utils import distinct


class LexicalEntry:

    def __init__(self, word, is_overt, nodes):
        assert isinstance(word, str)
        assert isinstance(is_overt, bool)
        assert isinstance(nodes, list)
        self.word = word
        self.is_overt = is_overt
        self.nodes = nodes


    def __str__(self):
        return str({'word': self.word,
                    'is_overt': self.is_overt,
                    'nodes': self.nodes})


class LexiconFormula(SMTFormula):
    """
    An SMT formula encoding an MG lexicon.
    """

    def create_lexicon(solver, pf_interface, params, verbose=False):
        str_eval = lambda s: s if type(s) is not str else eval(s)
        num_lex_nodes = ((len(pf_interface.overt_forms) * params['num_overt_lexical_entries_per_form'] +
                          len(pf_interface.covert_forms) * params['num_covert_lexical_entries_per_form'])
                         * params['max_num_features_per_lexical_entry'] + 2)
        lf = LexiconFormula(solver,
                            pf_interface,
                            num_lexicon_nodes=num_lex_nodes,
                            num_overt_lexical_entries_per_form=params['num_overt_lexical_entries_per_form'],
                            num_covert_lexical_entries_per_form=params['num_covert_lexical_entries_per_form'],
                            max_num_overt_pf_connections=params['max_num_overt_pf_connections'],
                            max_num_covert_pf_connections=params['max_num_covert_pf_connections'],
                            selectional_feature_labels=str_eval(params['selection_feature_labels']),
                            licensing_feature_labels=str_eval(params['licensing_feature_labels']),
                            factored_lexicon=True)

        # Add lexical entries for the overt (pronounced) phonetic forms.
        for word in pf_interface.overt_forms:
            for i in range(params['num_overt_lexical_entries_per_form']):
                lf.add_lexical_entry(word,
                                     is_overt=True,
                                     max_num_features=params['max_num_features_per_lexical_entry'])
                if verbose:
                    solver.log_msg("Added an overt lexical entry for the word: " + word)

        # Add lexical entries for the covert (unpronounced) phonetic forms.
        for word in pf_interface.covert_forms:
            for i in range(params['num_covert_lexical_entries_per_form']):
                lf.add_lexical_entry(word,
                                     is_overt=False,
                                     max_num_features=params['max_num_features_per_lexical_entry'])
                if verbose:
                    solver.log_msg("Added a covert lexical entry for the word: " + word)

        return lf


    def create_lexicon_from_spec(solver, lexicon_json, pf_interface, params, verbose=False):
        str_eval = lambda s: s if type(s) is not str else eval(s)
        lexicon_json = json.loads(lexicon_json)
        num_lex_nodes = len(lexicon_json) * params['max_num_features_per_lexical_entry'] + 2
        lf = LexiconFormula(solver,
                            pf_interface,
                            num_lexicon_nodes=num_lex_nodes,
                            selectional_feature_labels=str_eval(params['selection_feature_labels']),
                            licensing_feature_labels=str_eval(params['licensing_feature_labels']),
                            factored_lexicon=False)
        if verbose:
            solver.log_msg("Initialized the lexicon formula.")
        lf.init_spec_jsle_to_lfle = {}
        max_num_features = params['max_num_features_per_lexical_entry']
        for le in lexicon_json:
            is_overt = le['pf'] != pf_interface.EPSILON
            if verbose:
                solver.log_msg(f"[LexiconFormula] Added entry (is_overt={is_overt}) for item: {le}")
            #multiples = ... CONTINUE HERE!
            result = lf.add_lexical_entry(le['pf'], is_overt=is_overt, max_num_features=max_num_features)
            lf.init_spec_jsle_to_lfle[json.dumps(le)] = result
        return lf


    def __init__(self,
                 solver,
                 pfInterface,
                 num_lexicon_nodes,
                 selectional_feature_labels,
                 licensing_feature_labels,
                 factored_lexicon=True,
                 max_num_overt_pf_connections=None,
                 max_num_covert_pf_connections=None,
                 num_overt_lexical_entries_per_form=None,
                 num_covert_lexical_entries_per_form=None):
        super().__init__(solver)
        self.FACTORED_LEXICON = factored_lexicon
        self.pfInterface = pfInterface
        self.entries = []
        self.num_overt_lexical_entries_per_form = num_overt_lexical_entries_per_form
        self.num_covert_lexical_entries_per_form = num_covert_lexical_entries_per_form
        self.max_num_overt_pf_connections = max_num_overt_pf_connections
        self.max_num_covert_pf_connections = max_num_covert_pf_connections
        
        # Initialize Model Parameters
        self.num_lexicon_nodes = num_lexicon_nodes
        self.selectional_feature_labels = selectional_feature_labels
        self.licensing_feature_labels = licensing_feature_labels
        self.feature_labels = selectional_feature_labels + licensing_feature_labels + ['']

        # Initialize Sorts
        self.LNodeSort, self.nodes = self.create_finite_sort('LexiconNode', self.num_lexicon_nodes)
        self.LFeatureLabel, self.syn_feats = self.create_finite_sort('LexiconFeatureLabel', len(self.feature_labels))
        self.LTypeSort = self.create_datatype('LexiconNodeType',
                                              ['Terminal', 'Complete', 'Selector', 'Selectee', 'Licensor', 'Licensee', 'Inactive'])

        # Setup the syntactic features.
        self.selectional_syn_feats = self.syn_feats[:len(self.selectional_feature_labels)]
        self.licensing_syn_feats = self.syn_feats[len(self.selectional_feature_labels):-1]
        self.nil_syn_feature = self.syn_feats[-1]

        # Allocate the complete node and terminal node; the remainder of the
        # nodes can be allocated for differing purposes.
        self.allocated_nodes = set()
        self.unallocated_nodes = set(self.nodes)
        self.terminal_node, self.complete_node = self.__allocate_nodes__(2)
        assert len(self.allocated_nodes) == 2, "Expected 2 singletons to have been allocated."
        self.non_singleton_nodes = [x for x in self.unallocated_nodes]

        # Initialize Functions
        self.lnodeType = self.create_func('lnode_type', self.LNodeSort, self.LTypeSort)
        self.succ = self.create_func('successor', self.LNodeSort, self.LNodeSort)
        self.featLbl = self.create_func('feature_label', self.LNodeSort, self.LFeatureLabel)
        self.pf_map = self.create_func('pf_map',
                                       self.LNodeSort,
                                       self.pfInterface.PFNodeSort,
                                       BoolSort())
        mgsmt.formulas.derivationformula.DerivationFormula._init_cat_sort()
        self.cat_map = self.create_func('cat_map',
                                        self.LNodeSort,
                                        mgsmt.formulas.derivationformula.DerivationFormula.CatSort)
        self.head_movement = self.create_func('head_movement', self.LNodeSort, BoolSort())

        self.derivations = {}
        self.__add_initial_constraints__()

    def __allocate_nodes__(self, n):
        assert n > 0
        N = len(self.unallocated_nodes)
        if N < n:
            raise Exception(f"Couldn't allocate {n} nodes because only {N} nodes are unallocated.")
        nodes = [self.unallocated_nodes.pop() for i in range(n)]
        self.allocated_nodes.update(nodes)
        return nodes

    def get_feature_str(self, feature_label):
        for lbl, sf in zip(self.feature_labels, self.syn_feats):
            if str(feature_label) == str(sf):
                return lbl
        else:
            raise Exception("%r not in %r"%(pf_node, self.pf_nodes))

    def __l2s__(self):
        return {self.LTypeSort.Selector: '=',
                self.LTypeSort.Selectee: '~',
                self.LTypeSort.Licensor: '+',
                self.LTypeSort.Licensee: '-',
                self.LTypeSort.Complete: 'C'}

    def strToLType(self, s):
        if s[0] in ('<', '>'):
            s = s[1:] # Head movement is handled separately.
        s2l = {v:k for k,v in self.__l2s__().items()}
        return s2l.get(s)

    def ltypeToStr(self, term_type, term_feat_lbl, head_movement=False):
        if term_type in self.__l2s__():
            return (('<' if head_movement else '') + self.__l2s__()[term_type], term_feat_lbl)
        elif term_type in (self.LTypeSort.Inactive, self.LTypeSort.Terminal):
            return None
        raise Exception("Could not recognize: %r"%((term_type, term)))

    def enum_usable_nodes(self, is_start_node=None, is_overt=None):
        if is_start_node is not None:
            assert isinstance(is_start_node, bool)
        if is_overt is not None:
            assert isinstance(is_overt, bool)
        for le in self.entries:
            if is_overt is not None:
                if is_overt != le.is_overt:
                    continue
            for i, node in enumerate(le.nodes):
                if is_start_node is not None:
                    if is_start_node != (i == 0):
                        continue
                yield node

    def enum_entries(self, is_overt=None, word=None):
        if word is not None:
            assert isinstance(word, str)
        if is_overt is not None:
            assert isinstance(is_overt, bool)
        for le in self.entries:
            if is_overt is not None:
                if is_overt != le.is_overt:
                    continue
            if word is not None:
                if word != le.word:
                    continue
            yield le

    def __add_initial_constraints__(self):
        succ = self.succ
        cn = self.complete_node
        tn = self.terminal_node
        lnT = self.lnodeType
        s = self.solver

        with s.group(tag='Node Type Relations'):
            s.add_singleton(lnT(cn) == self.LTypeSort.Complete)
            s.add_singleton(lnT(tn) == self.LTypeSort.Terminal)
            s.add_conj(Distinct(lnT(x), self.LTypeSort.Complete, self.LTypeSort.Terminal)
                       for x in self.non_singleton_nodes)

        # Note: An inactive lexicon node is one that is not used in any derivation
        # (and thus wouldn't appear in the extracted lexicon when the model is evaluated).
        with s.group(tag='Inactive nodes are not a succ. to any node.'):
            s.add_conj(Implies(y == succ(x), lnT(y) != self.LTypeSort.Inactive)
                       for x, y in distinct(product(self.nodes, repeat=2)))
        with s.group(tag='Inactive nodes have the Terminal node as successor.'):
            s.add_conj(Implies(lnT(x) == self.LTypeSort.Inactive, succ(x) == tn) for x in self.nodes)
        with s.group(tag='The succ. of the Complete Node is the Terminal Node.'):
            s.add_singleton(succ(cn) == tn)
        with s.group(tag='The succ. of the Terminal Node is the Terminal Node.'):
            s.add_singleton(succ(tn) == tn)
        with s.group('The terminal node maps to the nil syntactic feature.'):
            s.add_singleton(self.featLbl(self.terminal_node) == self.nil_syn_feature)
        with s.group('The complete node maps to the nil syntactic feature.'):
            s.add_singleton(self.featLbl(self.complete_node) == self.nil_syn_feature)

        # REFACTORED-LEXICON
        with s.group(tag='REFACTORED LEXICON CONSTRAINTS'):
            s.add_conj([self.pf_map(x, self.pfInterface.null_pf_node) != \
                        Or([self.pf_map(x, y)
                            for y in self.pfInterface.non_null_nodes()])
                        for x in self.nodes])
            if not(self.FACTORED_LEXICON):
                # Each lexical entry can connect to exactly one of the pf-nodes.
                s.add_conj([PbEq([(self.pf_map(x, y), 1)
                                  for y in self.pfInterface.pf_nodes],
                                 k=1)
                            for x in self.nodes])
            else:
                # Each PF is restricted as to how many Lex. Nodes it may connect to.
                k_overt = self.max_num_overt_pf_connections
                if k_overt:
                    for pf_node in self.pfInterface.overt_pf_nodes:
                        s.add_singleton(PbLe([(self.pf_map(l_node, pf_node), 1) for l_node in self.nodes],
                                             k=k_overt))
                
                k_covert = self.max_num_covert_pf_connections
                if k_covert:
                    for pf_node in self.pfInterface.covert_pf_nodes:
                        s.add_singleton(PbLe([(self.pf_map(l_node, pf_node), 1) for l_node in self.nodes],
                                             k=k_covert))


    def prohibit_idle_entries(self):
        # All of the lexical entries must be used by at least one of the
        # derivations.
        s = self.solver
        with s.group("Prohibit idle entries."):
            s.add_conj([Or([df['bus'](d_node) == entry.nodes[0]
                            for df_id, df in self.derivations.items()
                            for d_node in df['formula'].nodes()])
                        for entry in self.entries])


    def add_lexical_entry(self, word, is_overt, max_num_features):
        assert isinstance(word, str)
        assert isinstance(is_overt, bool)
        assert isinstance(max_num_features, int)
        assert 0 < max_num_features

        nodes = self.__allocate_nodes__(max_num_features)
        le = LexicalEntry(word, is_overt, nodes)
        if le in self.entries:
            raise Exception("Could not add duplicate lexical entry: %r"%(le))
        self.entries.append(le)

        # Define shorthand for convenience and brevity.
        succ = self.succ
        cn = self.complete_node
        tn = self.terminal_node
        lnT = self.lnodeType
        pf_map = self.pf_map
        featLbl = self.featLbl
        pfi = self.pfInterface
        lts = self.LTypeSort
        start_node, tail_nodes = (le.nodes[0], le.nodes[1:])

        s = self.solver

        with s.group(tag='PF-Interface Constraints'):
            with s.group(tag="The first node in the lexical entry is associated with some PF."):
                # REFACTORED-LEXICON
                #s.add_conj([self.pf_map(start_node) == pfi.get_pf_node(word)])
                #if not(self.FACTORED_LEXICON):
                if not(self.FACTORED_LEXICON):
                    s.add_conj([self.pf_map(start_node, pfi.get_pf_node(word))])
                    # The following is a speedup by further restricting the
                    # values pf_map may take on.
                    s.add_conj([self.pf_map(start_node, pf_node) == (pf_node == pfi.get_pf_node(word))
                                for pf_node in pfi.non_null_nodes()])
                else:
                    s.add_conj([Implies(self.pf_map(start_node, p_node),
                                        self.pf_map(start_node, pfi.get_pf_node(word)))
                                for p_node in pfi.non_null_nodes()])
            with s.group(tag="The remaining nodes (i.e. the 'cdr') in the lex. entry is not assoc. with any PF."):
                # REFACTORED-LEXICON
                #s.add_conj(self.pf_map(x) == pfi.null_pf_node for x in tail_nodes)
                s.add_conj(self.pf_map(x, pfi.null_pf_node) for x in tail_nodes)
            with s.group(tag="Prior entries with the same word must be used first."):
                # If this lexical entry associates with the specified word, then
                # all earlier lexical entries associated with the specified word
                # must *also* associate with this word.
                prior_entries = [e for e in self.entries[:-1] if e.word == word]
                def bleep(x):
                    return And(self.pf_map(x, pfi.get_pf_node(word)),
                               self.LTypeSort.Inactive != self.lnodeType(x))
                s.add_singleton(Implies(bleep(start_node),
                                        And([bleep(entry.nodes[0]) for entry in prior_entries])))
            with s.group(tag="First node in lex. entry is active iff doesn't associate with Null PF node."):
                s.add_singleton(self.pf_map(start_node, self.pfInterface.null_pf_node) == \
                                (self.lnodeType(start_node) == self.LTypeSort.Inactive))

        
        with s.group(tag='Succ. Rels.'):
            with s.group(tag='THIS CONSTRAINT IS LIKELY NOT NEEDED. TRY REMOVING.'):
                s.add_conj(Not(succ(x) == y) for x, y in product(self.unallocated_nodes, le.nodes))
            s.add_conj(Or([succ(x) == y for y in (le.nodes[i+1], tn, cn)]) for i, x in enumerate(le.nodes[:-1]))
            s.add_singleton(Or([succ(le.nodes[-1]) == y for y in (tn, cn)]))
        with s.group(tag='Succ. Rels. for Non-singleton nodes.'):
            with s.group(tag='The succ. of a Selector or Licensor cannot be a Licensee.'):
                s.add_conj(Implies(Or(lnT(x) == lts.Selector, lnT(x) == lts.Licensor),
                                   lnT(succ(x)) != lts.Licensee)
                           for x in le.nodes)
            with s.group(tag='The succ. of a Selectee or Licensee is either a Licensee or Terminal.'):
                s.add_conj(Implies(Or(lnT(x) == lts.Selectee, lnT(x) == lts.Licensee),
                                   Or(lnT(succ(x)) == lts.Licensee, lnT(succ(x)) == lts.Terminal))
                           for x in le.nodes)
            with s.group(tag='Only a Selector can trigger head movement.'):
                s.add_conj(Implies(self.head_movement(x), lnT(x) == lts.Selector)
                           for x in le.nodes)
            with s.group(tag='Only the first syntactic feature in a sequence can trigger head-movement.'):
                s.add_conj([self.head_movement(x) == False for x in tail_nodes])
        with s.group(tag='Syn. feature label relations for non-singleton nodes'):
            with s.group(tag='nil feature iff the node has type Complete/Terminal/Inactive.'):
                s.add_conj((featLbl(x) == self.nil_syn_feature) ==\
                           Or([lnT(x) == ltype for ltype in (lts.Inactive, lts.Complete, lts.Terminal)])
                           for x in le.nodes)
            with s.group(tag='Licensors/Licensees cannot have selectional features'):
                s.add_conj(Implies(Or(lnT(x) == lts.Licensor, lnT(x) == lts.Licensee), featLbl(x) != f)
                           for x, f in product(le.nodes, self.selectional_syn_feats))
            with s.group(tag='Selectors/Selectees cannot have licensing features'):
                s.add_conj(Implies(Or(lnT(x) == lts.Selector, lnT(x) == lts.Selectee), featLbl(x) != f)
                           for x, f in product(le.nodes, self.licensing_syn_feats))

        return le


    def connect_derivation(self, df, verbose=True):
        """
        This method connects a derivation formula object to the lexicon. It does this by:
        (1) registering this derivation formula with the lexicon and ensuring that
            there are no duplicate registrations.
        (2) creating a new uninterpreted function, the 'bus', that maps derivation
            nodes to lexicon nodes.
        (3) adding constraints on this function to ensure that the structure of the
            derivation maps properly to the structure of the lexicon.
        """
        s = self.solver
        lnT = self.lnodeType
        lts = self.LTypeSort

        # (1) Register the derivation.
        if df.formula_name in self.derivations:
            assert False, "%r already connected to this lexicon."%(df.formula_name)
        self.derivations[df.formula_name] = {'formula': df}
        if verbose:
            s.log_msg("Connecting a new derivation: %r"%(df.formula_name))

        # (2) Create an uninterpreted function, 'bus', that maps the derivation
        #     nodes to the lexicon nodes.
        bus = self.create_func('D2L_Bus_der_%r'%(df.formula_name), df.NodeSort, self.LNodeSort)
        self.derivations[df.formula_name]['bus'] = bus

        # (3) Add constraints to the 'bus' function.
        def connect_entries(d_entry, l_entry):
            conj_terms = []
            # Connect the nodes that line up.
            for i, (d_node, l_node) in enumerate(zip(d_entry, l_entry.nodes)):
                disj_terms = [bus(d_node) == l_node]
                if (i > 0) or not(l_entry.is_overt):
                    disj_terms.append(bus(d_node) == self.terminal_node)
                    disj_terms.append(bus(d_node) == self.complete_node)
                conj_terms.append(Or(disj_terms))
            return And(conj_terms)

        with s.group(tag='Bus Constraints.'):
            with s.group(tag='Shortest Movement Condition (SMC)'):
                # Assume that move_loc(x) is above move_loc(y).
                s.add_conj(Implies(And(df.dominates(df.parent(df.move_loc(x)), df.move_loc(y)),
                                       df.dominates(df.parent(df.move_loc(y)), x)),
                                   self.featLbl(bus(df.move_loc(x))) != self.featLbl(bus(df.move_loc(y))))
                           for x, y in distinct(product(df.non6root6nodes(), repeat=2)))
            with s.group(tag='Connect Covert Node-Seq Entries'):
                s.add_conj(Or([connect_entries(d_entry, l_entry)
                               for l_entry in self.enum_entries(is_overt=False, word=None)])
                               for d_entry in df.enum_covert_node_seqs())
            with s.group(tag='Derivation nodes cannot map to unallocated lexicon nodes.'):
                s.add_conj(bus(d_node) != l_node for d_node, l_node in product(df.nodes(), self.unallocated_nodes))
            with s.group(tag="PFs must match on both sides of the bus."):
                # REFACTORED-LEXICON
                #s.add_conj(df.pf_map(x) == self.pf_map(bus(x)) for x in df.nodes())
                s.add_conj(self.pf_map(bus(x), df.pf_map(x)) for x in df.nodes())
            with s.group(tag="Inactive nodes maps to Terminal Lexicon node."):
                s.add_conj((df.head(d_node) == df.null_node) == (bus(d_node) == self.terminal_node)
                           for d_node in df.non6root6nodes())
            with s.group(tag="Null node maps to Terminal Lexicon node."):
                s.add_singleton(bus(df.null_node) == self.terminal_node)
            with s.group(tag="Mapping Head Movement."):
                s.add_conj(self.head_movement(bus(y)) == Or([df.head_movement(x) == y for x in df.lex1nodes()])
                           for y in df.lex1nodes())
            with s.group(tag="Non-projecting der. nodes either undergo movement or terminate their proj. chain."):
                s.add_conj(Implies(And(df.head(x) != df.null_node, Not(df.projects(x))),
                                   self.succ(bus(x)) == If(df.move_loc(x) != df.null_node,
                                                           bus(df.move_loc(x)),
                                                           self.terminal_node))
                           for x in df.nodes())
            with s.group(tag='Only the root node can map to the complete lexicon node.'):
                s.add_conj(Implies(bus(d_node) == self.complete_node, d_node == df.root_node)
                           for d_node in df.nodes())
            with s.group(tag='The root node maps to the Complete lex. node iff there is a parse.'):
                s.add_conj([If(df.head(df.root_node) == df.null_node,
                               lnT(bus(df.root_node)) == lts.Inactive,
                               lnT(bus(df.root_node)) == lts.Complete)])

        with s.group(tag="Merging nodes."):
            with s.group(tag='If any node has move_loc equal to non-proj. node, it cannot be a selectee.'):
                s.add_conj(Implies(df.move_loc(x) == y,
                                   lnT(bus(y)) == lts.Licensee)
                           for x, y in distinct(product(df.nodes(), repeat=2)))
            with s.group(tag='Lex. nodes cannot be Licensors or Licensees.'):
                s.add_conj(Distinct(lnT(bus(x)), lts.Licensor, lts.Licensee)
                           for x in df.lex1nodes())
            with s.group(tag='Map to the same (non-nil) feature label in the lexicon.'):
                s.add_conj(Implies(df.merged(x, y) != df.null_node,
                                   self.featLbl(bus(x)) == self.featLbl(bus(y)))
                               for x, y in distinct(product(df.nodes(), repeat=2)))
            with s.group(tag='(proj, non-proj) node have types (selector, selectee) or (licensor, licensee).'):
                s.add_conj(Implies(And(df.merged(x, y) != df.null_node, df.projects(x)),
                                   And(Or(And(lnT(bus(x)) == lts.Selector, lnT(bus(y)) == lts.Selectee),
                                          And(lnT(bus(x)) == lts.Licensor, lnT(bus(y)) == lts.Licensee))))
                               for x, y in distinct(product(df.nodes(), repeat=2)))
            with s.group(tag='The succ. of the result of merge is the succ. of the argument of merge that projects.'):
                s.add_conj(Implies(And(df.merged(x, y) != df.null_node, df.projects(x)),
                                   self.succ(bus(x)) == bus(df.merged(x, y)))
                           for x, y in distinct(product(df.nodes(), repeat=2)))

        with s.group(tag="Category Equality Across Derivations"):
            s.add_conj(df.cat_map(x) == self.cat_map(bus(x)) for x in df.lex1nodes())
