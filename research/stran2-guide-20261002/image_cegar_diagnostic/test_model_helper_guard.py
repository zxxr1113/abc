#!/usr/bin/env python3
"""Adversarial case-bound model executable guards and preserved default checks."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import diagnostic as d
from test_diagnostic import Circuit,p
import anytime as at
from product import write_aig
from test_anytime import rewrite_preserving_mtime_with_changed_ctime


class HelperGuardTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.directory=Path(self.tmp.name)
        self.helper=self.directory/'helper';self.helper.write_bytes(b'A'*16)
        self.binding=dict(sha256=d.sha(self.helper),identity=d.executable_identity(self.helper))
        self.a=Circuit(1,1,[(2,5)],[2],[6]);self.graph,self.base,self.step,_=p.compile_graph(self.a)
        self.candidate=dict(root=3,recipe=[],out=0)
        self.number=0

    def tearDown(self):self.tmp.cleanup()

    def process(self,command,**kwargs):
        Path(command[4]).write_text('query,result,conflicts,wall_s\n0,1,0,0.0\n')
        Path(command[5]).write_text(json.dumps(dict(query=0,values=[0,1,1]))+'\n')
        return SimpleNamespace(returncode=0)

    def invoke(self,binding=True,process=None):
        self.number+=1;out=self.directory/f'call_{self.number}'
        graph=p.Graph();graph.gates=list(self.graph.gates);graph.hash=dict(self.graph.hash)
        start=time.monotonic();deadline=at.Budget(start,start+30)
        options=dict(helper_binding=self.binding) if binding is True else {} if binding is False else dict(helper_binding=binding)
        with patch.object(d.subprocess,'run',side_effect=process or self.process):
            answer=d.collect_models(p,self.a,graph,self.base,self.step,[copy.deepcopy(self.candidate)],out,
                self.helper,deadline,dict(input_sha256='test-source'),**options)
        return out,answer

    def mutate(self):
        old=rewrite_preserving_mtime_with_changed_ctime(self.helper,b'B'*16)
        self.assertEqual(self.helper.stat().st_size,old.st_size)
        self.assertEqual(self.helper.stat().st_mtime_ns,old.st_mtime_ns)
        self.assertNotEqual(self.helper.stat().st_ctime_ns,old.st_ctime_ns)

    def test_fast_repeated_calls_do_not_hash_helper_and_keep_artifact_checks(self):
        with patch.object(d,'sha',wraps=d.sha) as hashed:
            outputs=[self.invoke(True) for _ in range(2)]
        paths=[Path(x.args[0])for x in hashed.call_args_list]
        self.assertNotIn(self.helper,paths)
        for out,(samples,report) in outputs:
            self.assertEqual(len(samples),1);self.assertEqual(report['models'],1)
            for name in ('models.cnf','models.queries','models.variables'):
                self.assertEqual(paths.count(out/name),2)
            provenance=json.loads((out/'provenance.json').read_text())
            self.assertEqual(provenance['helper_sha256'],self.binding['sha256'])
            self.assertEqual(provenance['helper_stat_identity'],list(self.binding['identity']))
            self.assertIn('case_entry_exit_and_controller_sha256',provenance['helper_guard_strategy'])

    def test_standalone_default_still_hashes_helper_before_and_after(self):
        with patch.object(d,'sha',wraps=d.sha) as hashed:out,_=self.invoke(False)
        self.assertEqual(sum(Path(x.args[0])==self.helper for x in hashed.call_args_list),2)
        self.assertEqual(json.loads((out/'provenance.json').read_text())['helper_guard_strategy'],
                         'standalone_full_sha256_before_and_after_each_invocation')

    def test_replacement_between_calls_rejected_without_rebinding(self):
        self.invoke(True)
        other=self.directory/'replacement';other.write_bytes(b'A'*16);other.replace(self.helper)
        with self.assertRaisesRegex(ValueError,'executable identity changed'):self.invoke(True)

    def test_in_place_same_length_restored_mtime_rejected_by_ctime(self):
        self.invoke(True);self.mutate()
        with self.assertRaisesRegex(ValueError,'executable identity changed'):self.invoke(True)

    def test_mutation_during_helper_execution_rejected(self):
        def process(command,**kwargs):
            result=self.process(command,**kwargs);self.mutate();return result
        with self.assertRaisesRegex(ValueError,'executable identity changed'):self.invoke(True,process)

    def test_exception_path_checks_anchored_identity_in_finally(self):
        def process(command,**kwargs):
            self.mutate();raise subprocess.TimeoutExpired(command,1)
        with self.assertRaisesRegex(ValueError,'executable identity changed'):self.invoke(True,process)

    def test_unmutated_timeout_is_still_timeout(self):
        def process(command,**kwargs):raise subprocess.TimeoutExpired(command,1)
        with patch.object(d,'executable_identity',wraps=d.executable_identity) as identity:
            with self.assertRaises(subprocess.TimeoutExpired):self.invoke(True,process)
        self.assertEqual(identity.call_count,3)

    def test_fast_mode_still_rejects_cnf_query_and_projection_file_drift(self):
        for index in (1,2,3):
            def process(command,**kwargs):
                result=self.process(command,**kwargs)
                with Path(command[index]).open('a') as stream:stream.write(' changed')
                return result
            with self.assertRaisesRegex(ValueError,'model source identity changed'):self.invoke(True,process)

    def test_fast_mode_still_independently_replays_models(self):
        def process(command,**kwargs):
            result=self.process(command,**kwargs)
            Path(command[5]).write_text(json.dumps(dict(query=0,values=[0,1,0]))+'\n')
            return result
        with self.assertRaisesRegex(ValueError,'SAT model violates source miter'):self.invoke(True,process)

    def test_malformed_binding_rejected(self):
        for binding in [dict(sha256='bad',identity=self.binding['identity']),
                        dict(sha256=self.binding['sha256'],identity=[1,2,3,4]),{}]:
            with self.assertRaises(ValueError):self.invoke(binding)


class CaseBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.directory=Path(self.tmp.name)
        self.source=self.directory/'source.aig'
        write_aig(self.source,dict(ni=1,nl=1,gates=[],outputs=[4],latches=[2]))
        self.helper=self.directory/'helper';self.helper.write_bytes(b'H'*16)
        self.solver=self.directory/'solver';self.solver.write_bytes(b'S'*16)
        self.hid,self.hh=at.bind_executable(self.helper);self.sid,self.sh=at.bind_executable(self.solver)
        self.case=dict(file='fixture.aig',loaded_AND=0,input=str(self.source),input_sha256=p.sha(self.source))
        self.config=p.Config();self.start=time.monotonic()
        self.out=self.directory/'transform';self.out.mkdir();(self.out/'chunks').mkdir()
        self.job=dict(case=self.case,config=self.config.__dict__,out=str(self.out),solver=str(self.solver),
            solver_sha256=self.sh,solver_identity=self.sid,image_model_solver=str(self.helper),
            image_model_solver_sha256=self.hh,image_model_solver_identity=self.hid,start=self.start,end=self.start+30,
            source_hashes={},chunk_roots=32)

    def tearDown(self):self.tmp.cleanup()

    def test_transform_full_sha_checks_helper_at_entry_and_normal_exit(self):
        with patch.object(at,'sha',wraps=at.sha) as hashed,patch.object(at,'emit'):
            self.assertEqual(at.transform(self.job),0)
        self.assertEqual(sum(Path(x.args[0])==self.helper for x in hashed.call_args_list),2)

    def test_entry_rejects_wrong_bound_helper_sha(self):
        self.job['image_model_solver_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'SHA changed'):at.transform(self.job)

    def test_exit_rejects_drift_even_without_model_calls(self):
        original=at.signatures
        def initialize(*args,**kwargs):
            answer=original(*args,**kwargs);self.helper.write_bytes(b'X'*16);return answer
        with patch.object(at,'signatures',side_effect=initialize),patch.object(at,'emit'):
            with self.assertRaisesRegex(ValueError,'identity changed'):at.transform(self.job)

    def test_controller_rechecks_helper_after_budget_exhaustion(self):
        plan=dict(runtime_source_hashes={},solver_sha256=self.sh,solver_identity=self.sid,
            image_model_solver=str(self.helper),image_model_solver_sha256=self.hh,image_model_solver_identity=self.hid)
        def exhausted(*args,**kwargs):
            self.helper.write_bytes(b'X'*16)
            return dict(status='BUDGET_EXHAUSTED',exit_code=-9,observed_checkpoints=[])
        with patch.object(at,'supervise',side_effect=exhausted):
            with self.assertRaisesRegex(ValueError,'identity changed'):
                at.run_case(self.case,self.directory/'controller',self.directory,plan,self.config,self.solver,None,32,120)


if __name__=='__main__':unittest.main()
