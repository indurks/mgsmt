#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
An SMT-model of a minimalist derivation.
"""

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#

import functools, itertools
from nltk.tree import Tree
from z3 import And, Or, Not, Implies, Xor, Distinct, If, PbEq, PbGe, PbLe
import mgsmt
from mgsmt.solver.solver_utils import distinct, ordered, same_node

import copy

class DerivationModel(object):

    def __init__(self, derivation_formula, model):
        assert isinstance(derivation_formula,
                          mgsmt.formulas.derivationformula.DerivationFormula)
        self.formula = derivation_formula
        self.model = model
        self.tree = None


    def process_le(self, le, lex_model, d_node):
        # TODO: Need to refactor/clean this up, it was inserted as a hack.
        le = copy.deepcopy(le)
        le['features'] = [lex_model.pp_term(f, LaTeX=False)
                          for f in le['features']]
        le['cat'] = str(le['cat'])
        # TODO: Note that we only want the PF associated with the head of the
        # d_node.
        df = self.formula
        pfi = df.pfInterface
        m_eval = self.model.evaluate
        pf_d_node = pfi.get_pf(m_eval(df.pf_map(df.head(d_node))))
        assert pf_d_node in le['pfs'], f"Expected {pf_d_node} to be in {le['pfs']}."
        le['pfs'] = [pf_d_node]
        return le


    def get_indexed_lexical_entry(self, node, lex_model):
        lexical_entry = self.process_le(self.get_lexical_entry(node, lex_model),
                                        lex_model,
                                        node)
        feature_index = self.get_seq_index(node)
        return (lexical_entry, feature_index)


    def localize_interface_conditions(self, lex_model):
        """
        For each Interface Condition, identify the point in the
        derivation where the relevant syntactic relation is established,
        and the heads of the two syntactic structures being merged
        together at that point in the derivation, and the topological
        relations between these points in the derivation, thereby
        imposing a partial order upon the interface conditions.
        """
        df = self.formula
        # Identify a set of probes from the formula ic_dict.
        ic_probes = dict(self.formula.enum_ic_probes())
        # Evaluate which node in the derivation tree each probe points to, and
        # identify the relevant lexical item.
        m_eval = self.model.evaluate

        def get_children(probe_node):
            for proj_node, nproj_node in distinct(itertools.product(df.nodes(), repeat=2)):
                term = And(df.head(proj_node) == df.head(probe_node),
                           df.parent(proj_node) == probe_node,
                           df.head(proj_node) != df.null_node,
                           df.merged(proj_node, nproj_node) == probe_node)
                if m_eval(term):
                    return (proj_node, nproj_node)
            else:
                assert False, f"Could not find children for the probe: {probe_node}"


        for probe, ic_pp in ic_probes.items():
            if m_eval(df.head(probe) != df.null_node):
                # Obtain the probe node and its lexical entry.
                ic_pp['probe'] = probe
                ic_pp['node'] = m_eval(probe)
                ic_pp['lexical_entry'] = self.process_le(self.get_lexical_entry(ic_pp['node'], lex_model),
                                                         lex_model,
                                                         ic_pp['node'])
                ic_pp['lexical_entry_str'] = self.get_lex_entry_str(ic_pp['node'], lex_model)

                # Identify the children of the probe node.
                (ic_pp['proj-node'], ic_pp['nproj-node']) = get_children(ic_pp['node'])
                
                # Obtain the projecting child's lexical entry and feature index.
                def get_vals(child_node):
                    # Obtain the child node's lexical entry and feature index.
                    cc = {}
                    (cc['lexical_entry'], cc['feature_index']) = self.get_indexed_lexical_entry(child_node, lex_model)
                    cc['str_repr'] = self.get_lex_entry_str(child_node,
                                                            lex_model,
                                                            feature_index=cc['feature_index'],
                                                            HTML=False)
                    return cc

                ic_pp['proj_child'] = get_vals(ic_pp['proj-node'])
                ic_pp['nproj_child'] = get_vals(ic_pp['nproj-node'])

                # Construct the new IC used to detect over-generations.
                sent = list(df.whitelisted_surface_forms[0]) + \
                  ["?" if df.ic_dict['sent_type'] == 'question' else "."]
                loc_cs = [[ic_pp['lc_type'],
                           {k:' '.join([word for word, idx in v])
                            for k, v in ic_pp['lc_args'].items()}]]
                cat_cs = copy.deepcopy(df.ic_dict['categorical_constraints'])
                ic_pp['constraint'] = {"sentence": ' '.join(sent),
                                       "locality_constraints": loc_cs,
                                       "categorical_constraints": cat_cs}
                if 'arg_label' in ic_pp:
                    ic_pp['constraint']['arg_label'] = ic_pp['arg_label']

        # Perform a topological sort on the identified nodes.
        ordered_nodes = {ic_probes[probe]['node']:idx
                         for idx, probe in enumerate(ic_probes)}

        def hierarchically_dominates(item_a, item_b):
            node_a, node_b = item_a[1]['node'], item_b[1]['node']
            if m_eval(node_a == node_b):
                return 0
            elif m_eval(df.dominates(node_a, node_b)):
                return 1
            elif m_eval(df.dominates(node_b, node_a)):
                return -1
            else:
                return 1 if ordered_nodes[node_a] < ordered_nodes[node_b] else -1

        return dict(sorted(ic_probes.items(),
                           key=functools.cmp_to_key(hierarchically_dominates)))


    def get_seq_index(self, d_node):
        m, df = self.model, self.formula
        i, x = 0, m.evaluate(df.head(d_node))
        if m.evaluate(x == df.null_node):
            return None
        while m.evaluate(x != d_node):
            if m.evaluate(df.move_loc(x) != df.null_node):
                x = m.evaluate(df.move_loc(x))
                i += 1
            elif m.evaluate(And(df.head(df.parent(x)) == df.head(x),
                                df.head(x) != df.null_node)):
                x = m.evaluate(df.parent(x))
                i += 1
            else:
                return None
        return i


    def get_decorated_pf(self, head_d_node, display_head_movement=True):
        m, df = self.model, self.formula

        # Obtain the pf for the head node.
        head_pf_nd = m.evaluate(df.pf_map(head_d_node))
        head_pf_str = df.pfInterface.get_pf(head_pf_nd)

        # See if this node receives a moving head.
        if display_head_movement:
            for x in df.lex1nodes():
                if m.evaluate(df.head_movement(x) == head_d_node):
                    return "%s+%s"%(self.get_decorated_pf(x), head_pf_str)
        return head_pf_str


    def get_lexical_entry(self, d_node, lex_model):
        m, df = self.model, self.formula
        h = m.evaluate(df.head(d_node))
        lf = lex_model.formula
        bus = lf.derivations[df.formula_name]['bus']
        if m.evaluate(h == df.null_node):
            return None
        l_node = m.evaluate(bus(h))
        if l_node not in lex_model.lexical_entries:
            raise Exception("Key Error: l_node=%r, d_node=%r"%(l_node, d_node))
        entry = copy.deepcopy(lex_model.lexical_entries[l_node])
        return entry


    def get_lexical_entry_components(self, d_node, lex_model, LaTeX=False, HTML=False):
        entry = self.get_lexical_entry(d_node, lex_model)
        pf_strs, feats, cat_str = lex_model.get_lexical_entry_components(entry, LaTeX=LaTeX, HTML=HTML)
        idx = self.get_seq_index(d_node)
        return {'pf_strs': pf_strs, 'feats': feats, 'cat_str': cat_str, 'idx': idx}

    def get_lex_entry_str(self, d_node, lex_model=None, feature_index=None, HTML=True, LaTeX=False):
        assert not(HTML and LaTeX), (HTML, LaTeX)

        m, df = self.model, self.formula
        h = m.evaluate(df.head(d_node))
        if m.evaluate(h == df.null_node):
            return None

        i = self.get_seq_index(d_node)
        if feature_index:
            i = feature_index

        if lex_model == None:
            head_cat_str = str(m.evaluate(df.cat_map(h)))
            return "%s_%d/%s"%(self.get_decorated_pf(h), i, head_cat_str)

        le_components = self.get_lexical_entry_components(d_node, lex_model, HTML=HTML, LaTeX=LaTeX)

        if i == 0:
            # Here we may need to handle displaying head movement.
            pf_str = self.get_decorated_pf(h)
            feat_str = ','.join(le_components['feats'])
            l_str = "%s/%s::%s"%(pf_str, le_components['cat_str'], feat_str) 
        else:
            pf_str = df.pfInterface.get_pf(m.evaluate(df.pf_map(h)))
            feat_str = "%s·%s"%(','.join(le_components['feats'][:i]),
                                ','.join(le_components['feats'][i:]))
            l_str = "%s/%s:%s"%(pf_str, le_components['cat_str'], feat_str)
        return f"<{l_str}>" if HTML else l_str


    def get_dtree(self, display_node_id=False, head_relabeling_map={}, lex_model=None):
        if self.tree != None:
            return self.tree

        # Reconstruct and Visualize the Derivation
        assert self.model != None

        def get_node_label(head_node, main_node):
            head_lbl = head_relabeling_map.get(head_node, head_node)
            if not display_node_id:
                return self.get_lex_entry_str(main_node, lex_model=lex_model)
            return "%r_%r"%(head_lbl, self.get_seq_index(main_node))

        def get_children(x):
            for c1, c2 in distinct(itertools.product(self.formula.non6root6nodes(), repeat=2)):
                if self.model.evaluate(x == self.formula.merged(c1, c2)):
                    if self.model.evaluate(self.formula.head(c1) == self.formula.head(x)):
                        if self.model.evaluate(self.formula.is_lexical(c1)):
                            return (c1, c2)
                        else:
                            return (c2, c1)
            return None

        def get_tree(x):
            children = get_children(x)
            h = self.model.evaluate(self.formula.head(x))
            if children == None:
                return get_node_label(h, x)
            return Tree(get_node_label(h, x), map(get_tree, children))

        self.tree = get_tree(self.formula.root_node)
        return self.tree


    def get_sentence(self):
        return ' '.join(self.formula.get_surface_forms())


    def pretty_print(self,
                     display_node_id=False,
                     head_relabeling_map={},
                     lex_model=None):
        self.get_dtree(display_node_id=display_node_id,
                       head_relabeling_map=head_relabeling_map,
                       lex_model=lex_model).pretty_print()


    def get_color_of_head(self, x_node):
        cat_names = ['C_declarative', 'C_question', 'T', 'v', 'V',
                     'P', 'D', 'N']
        color_names = ['#8dd3c7','#8dd3c7','#ffffb3','#bebada','#fb8072',
                       '#80b1d3','#fdb462','#b3de69']
        colors = dict(zip(cat_names, color_names))
        
        df = self.formula
        m_eval = self.model.evaluate
        if m_eval(x_node == df.null_node):
            return 'white'
        else:
            head_cat = str(m_eval(df.cat_map(x_node)))
            return colors[head_cat]
