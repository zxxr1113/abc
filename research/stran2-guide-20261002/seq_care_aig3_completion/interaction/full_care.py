"""Validated reuse of immutable whole-cut image answers; no new care proof."""
import csv,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def source(case):return Path(json.loads((D/'frozen_rules.json').read_text())['full_sources'][case['file']]['diagnostic'])
def replay_queries(case,g,queries,out,tag):
    src=source(case);cnf=out/f'{tag}.cnf';qfile=out/f'{tag}.queries';result=out/f'{tag}.results.csv'
    g.cnf(cnf);assert cnf.read_bytes()==(src/f'{tag}.cnf').read_bytes()
    qfile.write_text(str(len(queries))+'\n'+''.join(f'{i} {len(q)} '+' '.join(map(str,q))+'\n'for i,q in enumerate(queries)))
    assert qfile.read_bytes()==(src/f'{tag}.queries').read_bytes()
    result.write_bytes((src/f'{tag}.results.csv').read_bytes());rr=list(csv.DictReader(result.open()))
    assert [int(r['query'])for r in rr]==list(range(len(queries)))
    answers=[int(r['result'])for r in rr];assert all(x in (-1,0,1)for x in answers)
    stat=dict(json.loads((src/'result.json').read_text())['metrics'][tag+'_queries'])
    stat.update(replayed=True,replayed_source=str(src),replayed_result_sha256=sha(src/f'{tag}.results.csv'),process_wall_s=0.0,solve_wall_s=0.0)
    return answers,stat
def load_patterns(case,g,reset,step,out):
    src=source(case);p=json.loads((src/'image_proofs.json').read_text());assert p['input_sha256']==case['input_sha256']
    assert p['cnf_sha256']==sha(src/'image.cnf') and p['queries_sha256']==sha(src/'image.queries')
    assert (src/'image.cnf').read_bytes()==(out/'care.cnf').read_bytes()
    rr=list(csv.DictReader((src/'image.results.csv').open()));answers=p['answers'];order=p['query_order']
    assert [int(r['query'])for r in rr]==list(range(len(answers)))
    assert [int(r['result'])for r in rr]==answers and len(answers)==len(order) and len(answers)%2==0
    lines=(src/'image.queries').read_text().splitlines();assert int(lines[0])==len(answers)
    proven={}
    for i in range(0,len(answers),2):
        q=order[i];leaves=q['leaves'];pat=q['pattern']
        assert leaves==sorted(set(leaves)) and 3<=len(leaves)<=6 and 0<=pat<(1<<len(leaves))
        for j,(phase,mp) in enumerate([('reset',reset),('step',step)]):
            z=order[i+j];expected=[mp[v]^int(not(pat>>k&1))for k,v in enumerate(leaves)]
            assert z==dict(leaves=leaves,pattern=pat,phase=phase,literals=expected)
            assert list(map(int,lines[1+i+j].split()))==[i+j,len(leaves),*expected]
            assert answers[i+j]in(-1,0,1)
        if answers[i:i+2]==[-1,-1]:
            key=tuple(leaves);proven[key]=proven.get(key,0)|(1<<pat)
    assert proven=={tuple(z['leaves']):z['forbidden']for z in p['proven']}
    (out/'image_proofs.json').write_bytes((src/'image_proofs.json').read_bytes())
    return proven
