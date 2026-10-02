"""Owned-process monitor calibration, not a circuit benchmark."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch,MagicMock

import pilot_process as pp

class IdentityTests(unittest.TestCase):
    def test_reused_pid_rejected_while_reading(self):
        old=dict(pid=10,ppid=1,pgid=10,start='old');new=dict(old,start='new')
        with patch.object(pp,'identity',side_effect=[old,new]),patch.object(Path,'read_text',return_value='VmRSS:\t8192 kB\n'),\
             patch.object(Path,'read_bytes',return_value=b'python\0--worker-job\0expected\0'):
            self.assertIsNone(pp.proc_info(10,old))

    def test_only_owned_parent_chain_gets_commandline_reads(self):
        table={10:dict(pid=10,ppid=1,pgid=10,start='a'),11:dict(pid=11,ppid=10,pgid=11,start='b'),
               12:dict(pid=12,ppid=11,pgid=11,start='c'),90:dict(pid=90,ppid=1,pgid=90,start='outside')}
        def info(pid,expected):return dict(table[pid],rss_kib=1,cmd=['owned'])
        with patch.object(pp,'identity',side_effect=lambda pid:table.get(pid)),\
             patch.object(Path,'iterdir',return_value=iter([Path('/proc')/str(p)for p in table])),\
             patch.object(pp,'proc_info',side_effect=info)as inspected:
            result=pp.snapshot(10)
        self.assertEqual(set(result['processes']),{10,11,12});self.assertTrue(result['complete'])
        self.assertEqual({call.args[0]for call in inspected.call_args_list},{10,11,12})

    def test_vanished_owned_process_marks_sample_partial(self):
        table={10:dict(pid=10,ppid=1,pgid=10,start='a'),11:dict(pid=11,ppid=10,pgid=11,start='b')}
        with patch.object(pp,'identity',side_effect=lambda pid:table.get(pid)),\
             patch.object(Path,'iterdir',return_value=iter([Path('/proc/10'),Path('/proc/11')])),\
             patch.object(pp,'proc_info',side_effect=lambda pid,expected:dict(table[pid],rss_kib=1,cmd=[])if pid==10 else None):
            result=pp.snapshot(10)
        self.assertFalse(result['complete']);self.assertEqual(set(result['processes']),{10})

    def test_worker_pid_reuse_between_outer_and_subtree_sample_is_missing(self):
        root=dict(pid=10,ppid=1,pgid=10,start='root',rss_kib=1,cmd=['driver'])
        worker=dict(pid=11,ppid=10,pgid=11,start='old',rss_kib=2,cmd=['python','--worker-job','expected'])
        replaced=dict(worker,start='new',rss_kib=999999)
        child=MagicMock(pid=10,returncode=0);child.poll.side_effect=[None,0]
        with tempfile.TemporaryDirectory()as tmp,patch.object(pp.subprocess,'Popen',return_value=child),\
             patch.object(pp,'snapshot',side_effect=[dict(processes={10:root,11:worker},complete=True),dict(processes={11:replaced},complete=True)]),\
             patch.object(pp.time,'sleep'):
            result=pp.execute(['owned'],Path(tmp)/'log',10,worker_job='expected')
        self.assertIsNone(result['sampled_transform_tree_peak_rss_kib'])
        self.assertEqual(result['worker_process_bindings'],[])
        self.assertEqual(result['worker_identity_mismatch_samples'],1)

class OwnedTreeTests(unittest.TestCase):
    def test_nested_worker_child_and_unrelated_exclusion(self):
        preserve=os.environ.get('STRAN2_RSS_FIXTURE_OUT')
        if preserve:
            out=Path(preserve);out.mkdir(parents=True,exist_ok=False)
        else:
            temp=tempfile.TemporaryDirectory();self.addCleanup(temp.cleanup);out=Path(temp.name)
        marker=str(out/'job.json');pids=out/'pids.json'
        grand='import time; x=bytearray(16*1024*1024); x[::4096]=b"x"*(len(x)//4096); time.sleep(2)'
        worker=f'''import os,sys,subprocess,json,time
from pathlib import Path
x=bytearray(8*1024*1024);x[::4096]=b'x'*(len(x)//4096)
child=subprocess.Popen([sys.executable,'-B','-c',{grand!r}])
Path({str(pids)!r}).write_text(json.dumps(dict(worker=os.getpid(),grandchild=child.pid)))
child.wait()
'''
        launcher=f'''import subprocess,sys
child=subprocess.Popen([sys.executable,'-B','-c',{worker!r},'--worker-job',{marker!r}])
child.wait()
'''
        unrelated=subprocess.Popen([sys.executable,'-B','-c','import time; x=bytearray(32*1024*1024); time.sleep(5)',
                                    '--worker-job',marker])
        try:
            result=pp.execute([sys.executable,'-B','-c',launcher],out/'launcher.log',10,worker_job=marker)
            (out/'monitor.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
            expected=json.loads(pids.read_text());self.assertEqual(result['exit_code'],0)
            self.assertEqual(result['transform_rss_status'],'OBSERVED_SAMPLED')
            self.assertGreater(result['matched_worker_complete_samples'],0)
            self.assertEqual({r['pid']for r in result['worker_process_bindings']},{expected['worker']})
            observed={r['pid']for r in result['worker_peak_processes']}
            self.assertEqual(observed,{expected['worker'],expected['grandchild']});self.assertNotIn(unrelated.pid,observed)
            self.assertEqual(result['sampled_transform_tree_peak_rss_kib'],sum(r['rss_kib']for r in result['worker_peak_processes']))
            self.assertGreater(result['sampled_transform_tree_peak_rss_kib'],24*1024)
        finally:unrelated.terminate();unrelated.wait()

if __name__=='__main__':unittest.main()
