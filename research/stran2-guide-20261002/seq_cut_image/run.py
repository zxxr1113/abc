#!/usr/bin/env python3
"""Frozen paired offline runs; every case/arm owns a new output directory."""
import argparse,concurrent.futures as cf,datetime,hashlib,json,os,signal,socket,subprocess,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def cpu():
    v=list(map(int,Path('/proc/stat').read_text().splitlines()[0].split()[1:]));return sum(v[:8]),v[3]+v[4]
def preflight():
    a=cpu();time.sleep(1);b=cpu();busy=os.cpu_count()*(1-(b[1]-a[1])/(b[0]-a[0]));mem=int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:')))*1024
    st=os.statvfs('/dev/shm');disk=st.f_bavail*st.f_frsize
    assert busy+8<=240 and mem>8*2**30 and disk>4*2**30
    ps=subprocess.run(['ps','-eo','pid,ppid,pcpu,comm'],capture_output=True,text=True,check=True).stdout
    return dict(host=socket.gethostname(),pid=os.getpid(),cpus=os.cpu_count(),busy_cores=busy,available_memory_bytes=mem,shm_available_bytes=disk,loadavg=os.getloadavg(),process_snapshot=ps)
def execute(case,mode,run,rules):
    parent=run/mode/Path(case['file']).stem;parent.mkdir(parents=True,exist_ok=False);out=parent/'diagnostic'
    assert sha(case['input'])==case['input_sha256']
    cmd=[sys.executable,str(D/'diagnose.py'),'--case',case['file'],'--mode',mode,'--out',str(out),'--solver',rules['solver']['binary']]
    start=time.monotonic();utc=datetime.datetime.now(datetime.timezone.utc).isoformat();env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']= '1'
    with (parent/'process.log').open('w') as log:
        proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,cwd=D,env=env,start_new_session=True)
        write(parent/'process.json',dict(host=socket.gethostname(),pid=proc.pid,pgid=proc.pid,command=cmd,started_utc=utc,timeout_s=120,runner_sha256=sha(__file__),rules_sha256=sha(D/'frozen_rules.json'),input_sha256=case['input_sha256']))
        try:rc=proc.wait(timeout=120);status='exit'
        except subprocess.TimeoutExpired:
            # This process group was created above exclusively for this case.
            os.killpg(proc.pid,signal.SIGTERM)
            try:rc=proc.wait(timeout=5)
            except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);rc=proc.wait()
            status='timeout'
    result=dict(file=case['file'],family=case['family'],mode=mode,status=status,returncode=rc,wall_s=time.monotonic()-start,timeout_s=120,command=cmd,host=socket.gethostname(),input=case['input'],input_sha256=case['input_sha256'],source_and=case['source_and'],input_and=case['input_and'],diagnostic=str(out),process_log_sha256=sha(parent/'process.log'),complete=status=='exit' and rc==0 and (out/'result.json').is_file())
    if result['complete']:result['result_sha256']=sha(out/'result.json')
    write(parent/'outcome.json',result);print(mode,case['file'],status,rc,'complete',result['complete'],flush=True);return result
def main():
    p=argparse.ArgumentParser();p.add_argument('--pilot',action='store_true');args=p.parse_args();rules=read(D/'frozen_rules.json')
    assert socket.gethostname()==rules['solver']['host']=='shuguang'
    assert all(sha(p)==h for p,h in rules['dependencies'].items())
    assert sha(rules['solver']['binary'])==rules['solver']['binary_sha256']
    ldd=subprocess.run(['ldd',rules['solver']['binary']],capture_output=True,text=True,check=True).stdout;assert 'not found' not in ldd
    if not args.pilot:
        gate=read(D/'pilot_summary.json');assert gate['status']=='PASS' and gate['rules_sha256']==sha(D/'frozen_rules.json')
        review=read(D/'independent_preflight_review.json');assert review['status']=='PASS' and review['rules_sha256']==sha(D/'frozen_rules.json')
    cases=[c for c in rules['cases'] if not args.pilot or c['file'] in rules['pilot_cases']]
    ident=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'_shuguang_'+('pilot'if args.pilot else 'fixed55')
    run=D/'runs'/ident;run.mkdir(parents=True,exist_ok=False)
    write(run/'manifest.json',dict(host=socket.gethostname(),pid=os.getpid(),run=str(run),rules_sha256=sha(D/'frozen_rules.json'),runner_sha256=sha(__file__),solver=rules['solver'],solver_ldd=ldd,workers=8,modes=['pair','full'],cases=cases,preflight=preflight()))
    write(D/('pilot_identity.json'if args.pilot else 'run_identity.json'),dict(path=str(run),rules_sha256=sha(D/'frozen_rules.json')))
    results=[]
    with cf.ThreadPoolExecutor(max_workers=8) as pool:
        futures=[pool.submit(execute,c,m,run,rules)for c in cases for m in ['pair','full']]
        for f in cf.as_completed(futures):results.append(f.result())
    assert all(sha(p)==h for p,h in rules['dependencies'].items())
    assert sha(rules['solver']['binary'])==rules['solver']['binary_sha256']
    write(run/'complete.json',dict(planned=len(cases)*2,results=results,rules_sha256=sha(D/'frozen_rules.json'),dependencies_unchanged=True))
    print('complete',run,flush=True)
if __name__=='__main__':main()
