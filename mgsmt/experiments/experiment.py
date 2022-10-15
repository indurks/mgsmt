#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "Sagar Indurkhya"
__copyright__ = "Copyright 2018-2022, Sagar Indurkhya"
__email__ = "indurks@mit.edu"

#------------------------------------------------------------------------------#
import collections, copy, itertools, os, pathlib, pprint as pp, random, shutil
import subprocess, sys, time, traceback, uuid
from datetime import datetime
from multiprocessing.pool import Pool

from IPython.core.display import display, HTML
import simplejson as json
from z3 import set_param
from z3 import And, Or, Not, Implies, Xor, Distinct, If, PbEq, PbGe, PbLe

import mgsmt.grammar
import mgsmt.solver
import mgsmt.experiments
import mgsmt.formulas.pfinterfaceformula
import mgsmt.grammar.interfacecondition
import mgsmt.formulas.df_serialization as df_serialization
from mgsmt.views.latex_widget import LaTeXWidget
from mgsmt.views.view_utils import display_latex

#------------------------------------------------------------------------------#

def compile_dot_file(sent_idx, sent, img_desc, dot_fp, img_fp, verbose=False):
    import pygraphviz
    pygraphviz.AGraph(dot_fp).draw(img_fp, prog='dot')
    if verbose:
        return f"Image of the {img_desc} for sentence #{sent_idx+1}: '{sent}' written to {img_fp}"


class Experiment(object):

    def __init__(self, params=None, config_filename=None, other_args=None, verbose=False):
        self.verbose = verbose
        assert (params is None) != (config_filename is None)
        self._init_logging()
        if config_filename:
            self._parse_config_file(config_filename, other_args=other_args)
        elif params:
            self.params = params
            self.params.update(other_args)
        self.backup_of_params = copy.deepcopy(self.params)
        self._init_solver()
        self.output = {}


    def _init_logging(self):
        pathlib.Path('./logs').mkdir(exist_ok=True)
        ts_str = datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d_%Hh%Mm%Ss')
        unique_id = str(uuid.uuid4())
        self.logging_dir = f"./logs/exp_{ts_str}_{unique_id}"
        pathlib.Path(self.logging_dir).mkdir()
        self.logging_img_dir = self.logging_dir + '/imgs'
        pathlib.Path(self.logging_img_dir).mkdir()
        self.logging_summary_dir = self.logging_dir + '/summary'
        pathlib.Path(self.logging_summary_dir).mkdir(exist_ok=False)
        self.log_file = open(f"{self.logging_dir}/experiment_{ts_str}_{unique_id}.log", 'w')


    def _parse_config_file(self, config_filename, other_args=None):
        """
        Parse the JSON formatted configuration file to produce a
        dictionary of parameter labels and values. The argument
        other_args is used to override the values in the dictionary.
        """
        try:
            self.config_filename = config_filename
            with open(config_filename, 'r') as f_json:
                self.params = json.load(f_json)
            if other_args:
                self.params.update(other_args)
            self.log(msg='Successfully read the configuration file: ' + config_filename)
            for k, v in self.params.items():
                self.log(msg='Parameter: %s, Value: %r'%(k, v),
                         quiet=(k=='input_sequence'))
        except json.JSONDecodeError as e:
            self.log(msg='Error: unable to read the configuration file: ' + str(e))
            raise(e)

    def _init_solver(self):
        self.solver = mgsmt.solver.SMTSolver(parameters=self.params, log_fn=self.log)
        if self.params['smt.phase_selection.random_seed.enabled']:
            set_param('smt.phase_selection', random.randint(0, 2222))
        set_param('parallel.enable', True)
        set_param('sat.acce', True)
        if self.verbose:
            self.log(msg='Initialized the Solver.')

    def _init_grammar(self):
        self.grammar = mgsmt.grammar.Grammar(solver=self.solver,
                                             pf_interface_formula=self.pf_interface,
                                             params=self.params)
        if self.verbose:
            self.log(msg='Initialized the Grammar.')

        def viz(label, visualize=False):
            if not(visualize):
                return
            if self.params['display.jupyter-widgets']:
                self._visualize(label=label)
                self.serialize_images(label=label)

        self.optstack = mgsmt.grammar.OptimizationStack(grammar=self.grammar,
                                                        visualization_callback=viz,
                                                        verbose=self.verbose)
        if self.verbose:
            self.log(msg='Initialized the Optimization Stack.')


    def _init_interface_conditions(self):
        if isinstance(self.params['ics_to_use'], list):
            ics_to_use = self.params['ics_to_use']
        elif isinstance(self.params['ics_to_use'], str):
            import pynumparser
            ics_to_use = pynumparser.NumberSequence(int).parse(self.params['ics_to_use'])
        else:
            assert False, "Could not parse the 'ics_to_use' parameter."
        assert 0 < len(set(ics_to_use)) == len(ics_to_use), ics_to_use
        self.interface_conditions = [mgsmt.grammar.interfacecondition.InterfaceCondition.construct_ic(self.params['input_sequence'][i],
                                                                        self.params)
                                     for i in ics_to_use]
        if self.verbose:
            self.log(msg='Initialized the Interface Conditions.')
            for i, ic in enumerate(self.interface_conditions):
                self.log(msg='Interface Condition #%d. %s'%(i, ic.json_repr()))
        self.inputseqtableview = mgsmt.views.inputsequencetableview.InputSequenceTableView(self.interface_conditions,
                                                                                           display_index=False)
        if self.params['display.jupyter-widgets']:
            try:
                inputseq_latex_widget = LaTeXWidget(self.inputseqtableview,
                                                    label='input_sequence',
                                                    dir_name=self.logging_img_dir)
                inputseq_latex_widget.display()
            except:
                print("Ran into exception while trying to display the input sequence.")


    def _visualize(self, label, dir_name=None):
        if dir_name is None:
            dir_name = self.logging_img_dir
        try:
            self.gw = mgsmt.views.acq_model_widget.GrammarWidget(self.grammar)
            if self.params['display.jupyter-widgets']:
                self.gw.display()
                lm_view = mgsmt.views.lexiconmodellatexview.LexiconModelLaTeXView([self.grammar.lexicon_model])
                lm_view.display(dir_name=dir_name, file_name="%s_lexicon"%(label))
                lm_widget = LaTeXWidget(lm_view, label, dir_name)
                lm_widget.display()
        except:
            self.log(msg='Exception raised while displaying the GrammarWidget: '\
                     + str(sys.exc_info()[0]))
            traceback.print_exc()


    def log(self, **kwargs):
        # Construct the record to log.
        record = collections.OrderedDict()
        record.update(kwargs)
        ts = datetime.fromtimestamp(time.time())
        record['date'] = ts.strftime('%Y-%m-%d')
        record['time'] = ts.strftime('%Hh%Mm%Ss')
        if 'proc.id' in self.params:
            record['proc.id'] = self.params['proc.id']
        # Write the record to the log file.
        self.log_file.write(json.dumps(record) + '\n')
        self.log_file.flush()
        if not self.params['display.jupyter-widgets']:
            return
        # Print the record to the terminal.
        def fmt(k, title, suffix=""):
            if k not in record:
                return None
            elif isinstance(record[k], float):
                return "%s: %0.2f%s"%(title, record[k], suffix)
            return "%s: %s%s"%(title, str(record[k]), suffix)
        xs = [record['time'],
              fmt('check_time', 'Check', suffix='s'),
              fmt('z3_add_elapsed_time', 'Z3_add_time', suffix='s'),
              fmt('construct_time', 'Construct', suffix='s'),
              fmt('total_elapsed', 'Elapsed', suffix='s'),
              fmt('label', 'Lbl'),
              fmt('msg', 'Msg')]
        if not(kwargs.get('quiet', False)):
            print(", ".join([x for x in xs if x is not None]))


    def serialize_images(self, label, dir_name=None):
        if dir_name is None:
            dir_name = self.logging_img_dir
        if self.verbose:
            self.log(msg='Lexicon: ' + self.grammar.lexicon_model.json_repr())
        tasks = []
        # Serialize the graphviz representation.
        def serialize_gviz(gviz_view, fp, desc, sent):
            with open('%s.dot'%(fp), 'w') as f_gviz:
                f_gviz.write(str(gviz_view.graphviz_repr()))
                if self.verbose:
                    self.log(msg='%s dot file for the sentence: "%s" written to %s'%(desc, sent, f_gviz.name))
                tasks.append((i, v['sentence'], desc, f_gviz.name, '%s.svg'%(fp)))
        for i, (k, v) in enumerate(self.gw.sent_choices.items()):
            # Serialize the derivation model tree view.
            dt_fp = '%s/%s_sent-%d_derivation_tree'%(dir_name, label, i+1)
            serialize_gviz(gviz_view=v['dmtv'], fp=dt_fp, desc='Derivation Tree', sent=v['sentence'])
            # Serialize the derivation model node-seq view.
            ns_fp = '%s/%s_sent-%d_nodeseq_repr'%(dir_name, label, i+1)
            serialize_gviz(gviz_view=v['dmnsv'], fp=ns_fp, desc='NodeSeq Repr', sent=v['sentence'])
        # Compile the dot files and serialize the generated figures.
        #tPool = Pool(processes=os.cpu_count())
        with Pool(processes=os.cpu_count()) as pool:
            futures = [pool.apply_async(compile_dot_file, t) for t in tasks]
            pool.close()
            pool.join()
            results_of_tasks = [f.get() for f in futures]


    def _init_interfaces(self, include_ic_words=True, include_init_lexicon_words=True):
        all_words = set()
        if include_ic_words:
            ic_words = set(itertools.chain(*[ic.tokens() for ic in self.interface_conditions]))
            covert_pforms = set([mgsmt.formulas.pfinterfaceformula.PFInterfaceFormula.EPSILON])
            all_words.update(ic_words)
        if include_init_lexicon_words:
            init_lex_items = json.loads(self.params.get('initial_lexical_items', "[]"))
            for entry in init_lex_items:
                if entry['pf'] != mgsmt.formulas.pfinterfaceformula.PFInterfaceFormula.EPSILON:
                    all_words.add(entry['pf'])
        self.pf_interface = mgsmt.formulas.pfinterfaceformula.PFInterfaceFormula(solver=self.solver,
                                                                                 overt_forms=all_words,
                                                                                 covert_forms=covert_pforms)
        if self.verbose:
            self.log(msg='Initialized the PF and LF Interfaces.')


    def create_final_report(self, output_dir):
        self._visualize(label='final', dir_name=output_dir)
        self.serialize_images(label='final', dir_name=output_dir)
        n = len(self.grammar.derivation_models)
        lm = self.grammar.lexicon_model
        lmtv = mgsmt.views.lexiconmodeltableview.LexiconModelTableView(lexicon_model=lm)
        l_widget = LaTeXWidget(lmtv, f"lexicon_model_values", output_dir)
        l_widget.display()

        for i, (_, dm) in enumerate(self.grammar.derivation_models.items()):
            sent_idx = i + 1
            sent = self.interface_conditions[i].get_sentence()
            dmtv = mgsmt.views.derivationmodeltableview.DerivationModelTableView(dm,
                                                                                 sent_idx,
                                                                                 n,
                                                                                 sent,
                                                                                 lexicon_model=lm)
            latex_dm_widget = LaTeXWidget(dmtv, "BEEEEE", self.logging_img_dir)
            latex_dm_widget.display()

            lex_latex_src = dmtv.get_latex_source(sent_idx=sent_idx,
                                                  num_sents=n,
                                                  sent=sent,
                                                  verbose=True)
            mgsmt.views.view_utils.display_latex(lex_latex_src,
                                                 output_dir,
                                                 f"dtree_{sent_idx}_model_values",
                                                 debug=True)
            dom_mtv = mgsmt.views.binaryfunctableview.BinaryFuncTableView(dm)
            dom_latex_src = dom_mtv.latex_src()
            mgsmt.views.view_utils.display_latex(dom_latex_src,
                                                 output_dir,
                                                 f"dominates_{sent_idx}_model_values",
                                                 debug=True)

        cmds = [r'mogrify -border 300 -bordercolor white -pointsize 12 -annotate +100+100 %t -density 300 -format pdf -- *.svg',
                r'pdftk input_sequence.pdf final_lexicon.pdf *_derivation_tree.pdf cat output all_final_derivation_trees.pdf']
        for cmd in cmds:
            subprocess.check_call(cmd,
                                  stderr=subprocess.DEVNULL,
                                  stdout=subprocess.DEVNULL,
                                  cwd=output_dir,
                                  shell=True)


    def init_from_lexicon(self):
        json_strs = []
        for lex_fn in self.params['init_lexicons']:
            with open(lex_fn, 'r') as f_lex_json:
                json_strs.append(json.dumps(json.load(f_lex_json)))
                self.log(msg="Loading a pre-specified lexicon from: " + f_lex_json.name)

        lex_items = self.params.get('initial_lexical_items', None)
        if json_strs:
            lr = mgsmt.experiments.lexrepr.LexRepr(json_strs=json_strs)
        else:
            lr = mgsmt.experiments.lexrepr.LexRepr(lex_items=lex_items)

        if self.params['display.jupyter-widgets']:
            lmtv = mgsmt.views.lexiconmodellatexview.LexiconModelLaTeXView(lexicon_models=[lr])
            lmtv.display(dir_name=self.logging_img_dir, file_name="initial_lexicon")
            lm_widget = LaTeXWidget(lmtv, label='initial', dir_name=self.logging_img_dir)
            lm_widget.display()

        return lr


    def initialize_model(self, init_lexicon_from_spec=False):
        init_lr = None
        if self.params['init_from_lexicon']:
            init_lr = self.init_from_lexicon()
        else:
            self.log(msg="the experiment will not be initialized from a pre-specified lexicon.")
        self._init_interface_conditions()
        self._init_interfaces()
        self._init_grammar()
        self.grammar._init_lexicon(init_lex_repr=init_lr,
                                   init_lexicon_from_spec=init_lexicon_from_spec,
                                   verbose=self.verbose)


    def constrain_model_with_input_sequence(self,
                                            include_locality_constraints,
                                            include_sent_type_constraint,
                                            include_categorical_constraints,
                                            include_pf_constraints,
                                            alternating_ic_mode=False,
                                            model_values={}):
        if alternating_ic_mode:
            self.log(msg=f"Operating in alternating IC mode.")

        for i, ic in enumerate(self.interface_conditions):
            # Construct a derivation formula for the interface condition.
            self.log(msg=f"Processing Input {i+1}/{len(self.interface_conditions)}.")
            if alternating_ic_mode:
                include_locality_constraints = not(include_locality_constraints)
                include_sent_type_constraint = not(include_sent_type_constraint)
                include_categorical_constraints = not(include_categorical_constraints)
                include_pf_constraints = not(include_pf_constraints)
            self.grammar.add_interface_condition(ic,
                                                 include_locality_constraints=include_locality_constraints,
                                                 include_sent_type_constraint=include_sent_type_constraint,
                                                 include_categorical_constraints=include_categorical_constraints,
                                                 include_pf_constraints=include_pf_constraints)

            # Load model values if applicable.
            df_id = self.grammar.ic2df[ic.label]
            df_model_values = {k:v for k, v in model_values.items() if k == df_id}
            self.grammar.load_derivation_model_values(df_model_values)

            # Optionally evaluate the model and display the inferred grammar.
            if self.params['evaluate_intermediate_steps'] or ((i + 1 == len(self.interface_conditions)) and i > 0):
                print(f"i: {i}, and len(self.interface_conditions) = {len(self.interface_conditions)}.")
                print(f"self.params['evaluate_intermediate_steps'] = {self.params['evaluate_intermediate_steps']}.")
                self.grammar.evaluate()
                lex_fn = 'test-serialization-lexicon-step-%d.json'%(i+1)
                final_lexicon, per_dm_lexicons = self.grammar.extract_lexicon(lex_fn)
                self.output['intermediate_lexicon_%d'%(i+1)] = final_lexicon
                if i >= len(self.interface_conditions) - 1:
                    if self.params['display.jupyter-widgets'] and include_pf_constraints:
                        self._visualize(label='step-%d'%(i+1))
                        self.serialize_images(label='step-%d'%(i+1))
