#!/usr/bin/env python3
"""Permit scientific pilot timeouts while retaining the frozen algorithm/runner."""
import concurrent.futures as cf,datetime,os,socket,subprocess,sys
sys.dont_write_bytecode=True
import run as r
def main():
    D=r.D;rules=r.read(D/'frozen_rules.json');launch=r.read(D/'full_launch.json')
    assert r.sha(__file__)==launch['launcher_sha256'] and r.sha(D/'frozen_rules.json')==launch['rules_sha256']
    assert all(r.sha(p)==h for p,h in rules['dependencies'].items())
    assert r.sha(rules['solver']['binary'])==rules['solver']['binary_sha256']
    pilot=r.read(D/'pilot_summary.json');assert r.sha(D/'pilot_summary.json')==launch['pilot_summary_sha256']
    assert pilot['rules_sha256']==launch['rules_sha256']
    for c in pilot['cases']:
        assert c['arms']['pair']['status']=='complete' and c['arms']['pair']['legacy_candidates_exactly_equal'] and c['arms']['pair']['legacy_selected_exactly_equal']
        for a in c['arms'].values():assert a['status']=='complete' and a['returncode']==0 or a['status']=='timeout'
    review=r.read(D/'independent_full_launch_review.json');assert review['status']=='PASS' and review['full_launch_sha256']==r.sha(D/'full_launch.json')
    assert socket.gethostname()==rules['solver']['host']=='shuguang'
    ldd=subprocess.run(['ldd',rules['solver']['binary']],capture_output=True,text=True,check=True).stdout;assert 'not found' not in ldd
    ident=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'_shuguang_fixed55'
    out=D/'runs'/ident;out.mkdir(parents=True,exist_ok=False)
    r.write(out/'manifest.json',dict(host=socket.gethostname(),pid=os.getpid(),run=str(out),rules_sha256=r.sha(D/'frozen_rules.json'),runner_sha256=r.sha(D/'run.py'),launcher_sha256=r.sha(__file__),full_launch_sha256=r.sha(D/'full_launch.json'),solver=rules['solver'],solver_ldd=ldd,workers=8,modes=['pair','full'],cases=rules['cases'],preflight=r.preflight()))
    r.write(D/'run_identity.json',dict(path=str(out),rules_sha256=r.sha(D/'frozen_rules.json'),full_launch_sha256=r.sha(D/'full_launch.json')))
    results=[]
    with cf.ThreadPoolExecutor(max_workers=8)as pool:
        fs=[pool.submit(r.execute,c,m,out,rules)for c in rules['cases']for m in ['pair','full']]
        for f in cf.as_completed(fs):results.append(f.result())
    assert all(r.sha(p)==h for p,h in rules['dependencies'].items())
    assert r.sha(rules['solver']['binary'])==rules['solver']['binary_sha256']
    r.write(out/'complete.json',dict(planned=110,results=results,rules_sha256=r.sha(D/'frozen_rules.json'),dependencies_unchanged=True))
    print('complete',out,flush=True)
if __name__=='__main__':main()
