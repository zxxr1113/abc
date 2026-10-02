"""Separate-process regressions for auditor/runtime copies at distinct paths."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import audit_online_products as audit

PACKAGE=Path(__file__).resolve().parent.parent


def copy_package(target):
    # Source only, no historical runs, inputs, binaries, or compiled caches.
    for folder in ('nonlinear_divisors','image_cegar_diagnostic','free_domain_diagnostic',
                   'seq_cut_image','seq_care_synthesis','teacher_adaptive_tools'):
        (target/folder).mkdir(parents=True)
        for source in (PACKAGE/folder).iterdir():
            if source.is_file() and source.suffix in ('.py','.c','.sh'):
                shutil.copyfile(source,target/folder/source.name)


class BindingTests(unittest.TestCase):
    def run_child(self,body,mutate=False):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);source=root/'run_source';copy_package(source)
            target=source/'image_cegar_diagnostic/diagnostic.py'
            expected=audit.sha(target)
            if mutate:
                target.write_text(target.read_text()+f'\nPath({str(root/"executed")!r}).touch()\n')
            code=f'''import sys,json,types
from pathlib import Path
sys.path.insert(0,{str(PACKAGE/'image_cegar_diagnostic')!r})
import audit_online_products as audit
import audit_products
original=audit.audit_diagnostic
refs=(audit.load_runtime,audit.require,audit.sha,audit.write_json,audit_products.sha,audit_products.verify_source)
source=Path({str(source)!r});expected={expected!r};bound={{}}
{body}
'''
            result=subprocess.run([sys.executable,'-B','-c',code],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
            self.assertEqual(result.returncode,0,result.stdout)
            self.assertFalse((root/'executed').exists(),'unverified module code executed')
            return json.loads(result.stdout)

    def test_distinct_source_inline_import_preserves_audit_globals(self):
        result=self.run_child('''binding=audit.bind_runtime_model_replay(source,{'image_cegar_diagnostic/diagnostic.py':expected},bound)
p=audit.load_runtime(source)
import inline_models as im
assert Path(im.d.__file__).resolve()==source/'image_cegar_diagnostic/diagnostic.py'
assert im.d is not original
assert refs==(audit.load_runtime,audit.require,audit.sha,audit.write_json,audit_products.sha,audit_products.verify_source)
assert audit_products.sha.__globals__ is original.__dict__
assert audit_products.verify_source.__globals__ is original.__dict__
audit.verify_bound(bound)
assert audit.bind_runtime_model_replay(source,{'image_cegar_diagnostic/diagnostic.py':expected},bound)==binding
print(json.dumps(binding))''')
        self.assertTrue(result['audit_helpers_preserved'])
        self.assertTrue(result['strict_runtime_path_guard_unchanged'])

    def test_changed_run_module_rejects_before_execution(self):
        result=self.run_child('''try:audit.bind_runtime_model_replay(source,{'image_cegar_diagnostic/diagnostic.py':expected},bound)
except ValueError as error:
 assert 'hash mismatch before import' in str(error)
 assert sys.modules['diagnostic'] is original
 print(json.dumps({'rejected':True}))
else:raise AssertionError('changed source accepted')''',mutate=True)
        self.assertTrue(result['rejected'])

    def test_unrelated_cached_module_rejects_without_replacement(self):
        result=self.run_child('''other=types.SimpleNamespace(__file__='/unrelated/diagnostic.py')
sys.modules['diagnostic']=other
try:audit.bind_runtime_model_replay(source,{'image_cegar_diagnostic/diagnostic.py':expected},bound)
except ValueError as error:
 assert 'unrelated cached' in str(error)
 assert sys.modules['diagnostic'] is other
 print(json.dumps({'rejected':True}))
else:raise AssertionError('unrelated cached module replaced')''')
        self.assertTrue(result['rejected'])

    def test_spoofed_target_path_is_not_an_authenticated_module(self):
        result=self.run_child('''other=types.SimpleNamespace(__file__=str(source/'image_cegar_diagnostic/diagnostic.py'))
sys.modules['diagnostic']=other
try:audit.bind_runtime_model_replay(source,{'image_cegar_diagnostic/diagnostic.py':expected},bound)
except ValueError as error:
 assert 'unrelated cached' in str(error)
 assert sys.modules['diagnostic'] is other
 print(json.dumps({'rejected':True}))
else:raise AssertionError('spoofed path accepted as authenticated code')''')
        self.assertTrue(result['rejected'])


@unittest.skipUnless(os.environ.get('STRAN2_INLINE_SOLVER') and os.environ.get('STRAN2_ABC'),
                     'requires STRAN2_INLINE_SOLVER and STRAN2_ABC')
class ActualCliTests(unittest.TestCase):
    def test_actual_cli_two_source_roots_with_enabled_checkpoint(self):
        preserve=os.environ.get('STRAN2_AUDIT_CLI_FIXTURE_OUT')
        if preserve:
            root=Path(preserve);root.mkdir(parents=True,exist_ok=False)
        else:
            tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup);root=Path(tmp.name)
        package=root/'original_package';copy_package(package)
        p=audit.load_runtime(PACKAGE)
        from product import write_aig
        source=package/'inputs/first_seq/tiny.aig';source.parent.mkdir(parents=True)
        write_aig(source,dict(ni=2,nl=2,gates=[(2,6),(4,8),(10,12)],outputs=[14],latches=[2,2]))
        loaded=package/'inputs/loaded/tiny.aig';loaded.parent.mkdir();shutil.copyfile(source,loaded)
        audit.write_json(package/'cases.json',dict(cases=[dict(file='tiny.aig',family='synthetic',
            first_seq_path='inputs/first_seq/tiny.aig',first_seq_sha256=audit.sha(source),
            loaded_path='inputs/loaded/tiny.aig',loaded_sha256=audit.sha(loaded),loaded_AND=3)]))
        run=root/'transform';out=root/'audit'
        solver=str(Path(os.environ['STRAN2_INLINE_SOLVER']).resolve());abc=str(Path(os.environ['STRAN2_ABC']).resolve())
        def execute(command,label):
            result=subprocess.run(command,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
            (root/(label+'.log')).write_text(result.stdout)
            audit.write_json(root/(label+'.command.json'),command)
            self.assertEqual(result.returncode,0,result.stdout)
        execute([sys.executable,'-B',str(package/'nonlinear_divisors/anytime.py'),
                 '--case','tiny.aig','--out',str(run),'--solver',solver,'--abc',abc,
                 '--inline-image-models','--predecessor-free','--workers','1','--wall-seconds','30',
                 '--dsec-seconds','30'],'transform')
        original=json.loads((run/'tiny/result.json').read_text())
        self.assertEqual(original['status'],'COMPLETE')
        selection=json.loads((Path(original['selected_checkpoint']['directory'])/'selection.json').read_text())
        self.assertTrue(selection['selected'])
        self.assertTrue(all('free_domain' in c for c in selection['selected']))
        # The real script entry point starts in the auditor's source root, then
        # reads a distinct run-local snapshot. No in-process helper shortcut.
        execute([sys.executable,'-B',str(PACKAGE/'image_cegar_diagnostic/audit_online_products.py'),
                 '--run',str(run),'--out',str(out),'--solver',solver,'--abc',abc,
                 '--proof-seconds','30','--dsec-seconds','30'],'audit')
        result=json.loads((out/'tiny/result.json').read_text())
        self.assertEqual(result['status'],'ATTRIBUTION_AUDIT_COMPLETE')
        self.assertIsInstance(result['validated_conditional_fresh_build_marginal'],int)
        plan=json.loads((out/'plan.json').read_text());binding=plan['model_replay_module_binding']
        self.assertEqual(Path(binding['file']),run/'source/image_cegar_diagnostic/diagnostic.py')
        self.assertNotEqual(Path(binding['audit_helper_file']),Path(binding['file']))
        self.assertEqual(json.loads((out/'integrity.json').read_text())['status'],'PASS')
        audit.write_json(root/'fixture_result.json',dict(status='PASS',separate_process_cli=True,
            distinct_auditor_runtime_roots=True,enabled_selected_candidates=len(selection['selected']),
            model_replay_module_binding=binding,formal_pilot=False))


if __name__=='__main__':unittest.main()
