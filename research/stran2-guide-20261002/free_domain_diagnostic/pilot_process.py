"""Owned process supervision and PPid-based Linux RSS sampling for new pilots.

Some executors omit /proc/PID/task/TID/children. Use kernel PPid/start tokens;
read command lines/RSS only for a process tree rooted at our launched child.
"""
import hashlib
import os
from pathlib import Path
import signal
import subprocess
import time

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def identity(pid):
    try:
        row=(Path('/proc')/str(pid)/'stat').read_text().rsplit(')',1)[1].split()
        return dict(pid=int(pid),ppid=int(row[1]),pgid=int(row[2]),start=row[19])
    except (FileNotFoundError,ProcessLookupError,PermissionError,IndexError,ValueError):return None

def proc_info(pid,expected=None):
    before=identity(pid)
    if before is None or (expected is not None and before!=expected):return None
    try:
        root=Path('/proc')/str(pid);rss=next((int(line.split()[1])for line in(root/'status').read_text().splitlines()if line.startswith('VmRSS:')),None)
        cmd=[x.decode(errors='replace')for x in(root/'cmdline').read_bytes().split(b'\0')if x]
        if identity(pid)!=before:return None
        return dict(before,rss_kib=rss,cmd=cmd)
    except (FileNotFoundError,ProcessLookupError,PermissionError):return None

def snapshot(pid):
    root=identity(pid)
    if root is None:return dict(processes={},complete=False)
    table={}
    for path in Path('/proc').iterdir():
        if path.name.isdigit():
            row=identity(int(path.name))
            if row is not None:table[row['pid']]=row
    if table.get(pid)!=root:return dict(processes={},complete=False)
    wanted={pid};changed=True
    while changed:
        added={child for child,row in table.items()if row['ppid']in wanted}-wanted
        changed=bool(added);wanted.update(added)
    observed={}
    for child in wanted:
        row=proc_info(child,table[child])
        if row is not None:observed[child]=row
    if identity(pid)!=root or pid not in observed:return dict(processes={},complete=False)
    # Do not retain a descendant whose observed parent chain vanished/reused.
    connected={pid};changed=True
    while changed:
        added={child for child,row in observed.items()if row['ppid']in connected}-connected
        changed=bool(added);connected.update(added)
    result={child:observed[child]for child in connected}
    return dict(processes=result,complete=connected==wanted and all(r['rss_kib']is not None for r in result.values()))

def descendants(pid):return snapshot(pid)['processes']

def stop_owned(process,owned):
    owned.update(descendants(process.pid));groups={}
    for pid,old in owned.items():
        now=proc_info(pid)
        if now and now['start']==old['start']and now['pgid']==old['pgid']and now['pgid']in owned:
            groups[now['pgid']]=owned[now['pgid']]['start']
    for sig in(signal.SIGTERM,signal.SIGKILL):
        for pid,old in reversed(list(owned.items())):
            now=identity(pid)
            if now and now['start']==old['start']:
                try:os.kill(pid,sig)
                except ProcessLookupError:pass
        for group,start in groups.items():
            if group==os.getpgrp():continue
            now=identity(group)
            if now is not None and now['start']!=start:continue
            try:os.killpg(group,sig)
            except ProcessLookupError:pass
        if sig==signal.SIGTERM:time.sleep(.2)
    if process.poll()is None:process.kill()
    process.wait(timeout=5)

def execute(command,log_path,watchdog_seconds,worker_job=None):
    start=time.monotonic();owned={};peak_all=peak_worker=0;samples=partial=worker_samples=identity_mismatches=0;bindings={};timeout=False;peak_processes=[];sampling_work=0.0
    with Path(log_path).open('w')as stream:
        process=subprocess.Popen(command,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
        try:
            while process.poll()is None:
                sampling_start=time.monotonic()
                sample=snapshot(process.pid);tree=sample['processes'];owned.update(tree);samples+=1
                partial+=not sample['complete']
                if sample['complete']:peak_all=max(peak_all,sum(r['rss_kib']for r in tree.values()))
                if worker_job:
                    for pid,row in tree.items():
                        cmd=row['cmd']
                        if '--worker-job'not in cmd:continue
                        index=cmd.index('--worker-job')
                        if index+1>=len(cmd)or cmd[index+1]!=worker_job:continue
                        sub=snapshot(pid)
                        subroot=sub['processes'].get(pid)
                        if subroot is None or any(subroot[k]!=row[k]for k in ('pid','ppid','pgid','start')):
                            identity_mismatches+=1;continue
                        if sub['complete']:
                            worker_samples+=1;rss=sum(r['rss_kib']for r in sub['processes'].values())
                            if rss>peak_worker:
                                peak_worker=rss
                                peak_processes=[{k:r[k]for k in ('pid','ppid','start','rss_kib')}for r in sub['processes'].values()]
                            bindings[(pid,row['start'])]=dict(pid=pid,start=row['start'],worker_job=worker_job)
                sampling_work+=time.monotonic()-sampling_start
                if time.monotonic()-start>watchdog_seconds:
                    timeout=True;stop_owned(process,owned);break
                time.sleep(.1)
        except BaseException:
            stop_owned(process,owned);raise
    return dict(command=command,exit_code=process.returncode,status='INFRASTRUCTURE_TIMEOUT'if timeout else'EXIT',
        wall_s=time.monotonic()-start,log_sha256=sha(log_path),samples=samples,partial_samples_skipped=partial,
        sampled_all_process_tree_peak_rss_kib=peak_all or None,
        sampled_transform_tree_peak_rss_kib=(peak_worker or None)if len(bindings)<=1 else None,
        matched_worker_complete_samples=worker_samples,worker_process_bindings=list(bindings.values()),
        worker_identity_mismatch_samples=identity_mismatches,
        worker_peak_processes=peak_processes if len(bindings)<=1 else [],sampling_interval_s=.1,
        sampling_work_wall_s=sampling_work,
        transform_rss_status='OBSERVED_SAMPLED'if peak_worker and len(bindings)==1 else'MISSING_OR_AMBIGUOUS',
        memory_note='100ms requested interval plus observer work; sampled complete observed PPid/start-token tree RSS sum. Shared pages double counted; short-lived peaks may be missed. Missing/partial-only observations remain null. Observer work is not subtracted from worker deadlines or driver wall time.')
