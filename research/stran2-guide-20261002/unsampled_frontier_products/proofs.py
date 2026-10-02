"""Fresh immutable proof batches for separately costed Build/Direct audit."""
import copy
import csv
from pathlib import Path
import subprocess
import time
from support import *
STATUS={-1:'UNSAT',0:'UNKNOWN',1:'SAT'}

def fresh_proofs(p,a,ia,candidates,solver,out,deadline,bindings,build):
    out=Path(out);out.mkdir();candidates=copy.deepcopy(candidates)
    g,base,image,reset=p.compile_graph(a);queries=[];order=[]
    for index,c in enumerate(candidates):
        deadline.remaining()
        for phase,mapping in [('free',base),('reset',reset),('step',image)]:
            miter=g.xor(mapping[c['root']],p.graph_recipe(g,mapping,c['recipe'],c['out']))
            order.append(dict(row=len(queries),candidate_index=index,candidate_id=[c['root'],c['recipe'],c['out']],phase=phase,assumptions=[miter]))
            queries.append([miter])
    cnf,qpath,rpath=out/'obligations.cnf',out/'obligations.queries',out/'obligations.results.csv'
    g.cnf(cnf)
    with qpath.open('x') as f:
        f.write(str(len(queries))+'\n')
        for i,q in enumerate(queries):f.write(f'{i} 1 {q[0]}\n')
    write_new(out/'query_order.json',order);write_new(out/'candidates.unproved.json',candidates)
    before=Bindings(bindings.files)
    for path in (cnf,qpath,out/'query_order.json',out/'candidates.unproved.json'):before.add(path)
    before.check(deadline);start=time.monotonic()
    if queries:
        with (out/'solver.log').open('x') as log:
            proc=subprocess.run([str(solver),str(cnf),str(qpath),str(rpath)],stdout=log,stderr=subprocess.STDOUT,
                                timeout=min(120,deadline.remaining()),check=False)
        require(proc.returncode==0,'fresh audit proof solver failed')
    else:
        with rpath.open('x') as f:f.write('query,result,conflicts,wall_s\n')
    solvewall=time.monotonic()-start;before.check(deadline)
    with rpath.open() as f:rows=list(csv.DictReader(f))
    require([int(r['query']) for r in rows]==list(range(len(queries))),'missing/reordered audit proof results')
    answers=[int(r['result']) for r in rows];require(all(x in STATUS for x in answers),'invalid audit proof status')
    before.add(rpath);accepted=[]
    cnf_hash,qhash,rhash,solverhash=sha(cnf),sha(qpath),sha(rpath),sha(solver)
    context_hash=digest(bindings.files)
    for i,c in enumerate(candidates):
        triple=answers[3*i:3*i+3]
        if 'free_witness' in c:
            w=c['free_witness'];v=ia.values(w['inputs'],w['state'])
            require(v==a.step(w['inputs'],w['state'])[2] and
                    (v[c['root']],independent_recipe(c['recipe'],c['out'],v))==(w['root'],w['replacement']) and
                    w['root']!=w['replacement'],'independent full source witness fails')
            require(triple[0]!=-1,'fresh COMB UNSAT contradicts independently replayed witness')
        c['source_proof']=copy.deepcopy(c.get('proof'))
        c['proof']={**dict(zip(('free','reset','step'),map(STATUS.get,triple))),
                    'free_witness_replayed':'free_witness' in c}
        c['audit_receipts']={phase:dict(cnf_sha256=cnf_hash,queries_sha256=qhash,results_sha256=rhash,
            solver_sha256=solverhash,row=3*i+j,assumptions=queries[3*i+j],result=STATUS[triple[j]],
            source_context_sha256=context_hash) for j,phase in enumerate(('free','reset','step'))}
        c['qualified_offline_opportunity']=triple==[1,-1,-1]
        if build:
            require(triple==[1,-1,-1] and c['proof']['free_witness_replayed'],'fresh Build reproof not SAT/UNSAT/UNSAT')
            accepted.append(c)
        elif triple[1:]==[-1,-1] and c['conservative_gain']>0:accepted.append(c)
        deadline.remaining()
    write_new(out/'candidates.json',candidates);before.add(out/'candidates.json')
    report=dict(candidates=len(candidates),queries=len(queries),accepted=len(accepted),solver_process_wall_s=solvewall,
        solver_internal_wall_s=sum(float(r['wall_s']) for r in rows),conflicts=sum(int(r['conflicts']) for r in rows),
        statuses={STATUS[x]:answers.count(x) for x in STATUS},conflicts_per_query=1000,
        source_bindings=bindings.files,proof_bindings=before.files,
        direct_free_unknown_accepted=sum(c['proof']['free']=='UNKNOWN' for c in accepted) if not build else 0)
    write_new(out/'report.json',report);return accepted,report
