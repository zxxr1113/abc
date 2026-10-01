#!/usr/bin/env python3
"""Read-only parameter/source audit of a completed materialized-helper run."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import audit

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--evidence', type=Path, required=True)
parser.add_argument('--frozen-source', type=Path, required=True)
parser.add_argument('--repo', type=Path, required=True)
args = parser.parse_args()
out, root = args.evidence.resolve(), args.repo.resolve()
p, prod, at = audit.load_runtime(args.frozen_source.resolve())
results = json.loads((out / 'results.json').read_text())
ranges = {
    'src/base/abci/abc.c': [(41844,41900),(42066,42116)],
    'src/proof/cec/cecCore.c': [(186,218)],
    'src/proof/cec/cecCorr.c': [(437,462),(466,590),(677,695),(1379,1415),(1434,1481),(1495,1530),(1680,1700),(1987,2072),(2308,2349),(2688,2704),(2757,2769),(2793,2803)],
    'src/proof/cec/cecClass.c': [(938,978),(989,1079)],
    'src/proof/cec/cecMan.c': [(199,219)],
    'src/proof/cec/cecSeq.c': [(137,173)],
}
sources = {}
for file, spans in ranges.items():
    lines = (root / file).read_text().splitlines()
    sources[file] = dict(sha256=p.sha(root / file),
        git_tracked_unmodified=subprocess.check_output(['git','diff','--',file],cwd=root,text=True)=='',
        excerpts=[dict(first_line=a,last_line=b,text='\n'.join(f'{i+1}: {lines[i]}' for i in range(a-1,b))) for a,b in spans])
verified = []
for result in results:
    for row in result['scorr_rounds']:
        text = (out / result['case'] / f"round_{row['round']:03d}.log").read_text()
        actual = re.search(r'Conf =\s*(\d+)\. Fr = (\d+)\. Lcorr = (\d+)\. Ring = (\d+)\. CSat = (\d+)\. Oracle = (\d+)\. Dyn = (\d+)\.', text)
        p.require(actual is not None and tuple(map(int,actual.groups())) == (1000,1,0,1,1,0,0), 'runtime parameters differ')
        verified.append(dict(case=result['case'],round=row['round'],actual=actual.group(0)))
p.write_json(out / 'parameter_evidence.json', dict(
    git_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
    abc_sha256=p.sha(root / 'abc'), sources=sources, runtime_log_checks=verified,
    notes=['Ordinary &scorr entry in repository binary; no -i/-o/-p/-k or scorr2 flags; verbose only',
           'CLI -F sets nFrames and -C sets nBTLimit; logs confirm Fr1/Conf1000; default nPrefix=0 from memset',
           'Ordinary induction calls CBS; ordinary nonempty base BMC calls TAS with the same 1000 limit',
           'No production/source instrumentation was added for this experiment']))
wb = next(x for x in results if x['case'] == '060_wb_dma')
a = p.Aiger(root / 'research/stran2-guide-20261002/inputs/first_seq/060_wb_dma.aig')
c = json.loads((out / '060_wb_dma/selected.json').read_text())[0]
_, _, values = a.step(c['free_witness']['inputs'],c['free_witness']['state'])
node = wb['pairs'][0]['helper_literal'] // 2
fanins = a.gates[node - a.ni - a.nl - 1]
p.write_json(out / 'wb_diagnostic.json', dict(
    root=c['root'], helper_original_node=node, helper_original_literal=2*node,
    helper_original_fanins=fanins, fanin_nodes=[x//2 for x in fanins],
    helper_depends_on_root=c['root'] in p.Structure(a).tfi([node]),
    source_input_sha256=wb['input_sha256'],recipe=c['recipe'],out=c['out'],
    free_witness_root=values[c['root']],free_witness_helper=values[node],
    existing_later_alias=True,
    prior_metric_scope='EARLIER_ID_RECIPE_SCOPE_PENDING_GLOBAL_STRUCTURAL_ALIAS_AUDIT',
    diagnostic_replay=json.loads((out / 'diagnostic_wb/result.json').read_text()),
    mechanism={
        'initial_class_assignment':'Both original ANDs enter candidate-constant class by source; exact later membership not emitted',
        'initial_simulation':'Zero-reset sequential; a genuinely image-valid equality should survive these samples (source/mathematical inference, not per-node trace)',
        'direct_root_helper_attempt':'UNKNOWN_NO_PER_PAIR_INSTRUMENTATION',
        'ordinary_induction_solver':'Cbs_ManSolveMiterNc, C1000',
        'ordinary_nonempty_base_solver':'Tas_ManSolveMiterNc, C1000',
        'observed_unknown_conflict_outcomes':'None in saved wb verbose induction rounds; f=0 throughout',
        'resimulation_loss_hypothesis':'Source full resimulation refines at f=0 after loading arbitrary predecessor-state induction CEX; valid reset/image relations with free-state SAT can split there. Plausible mechanism, exact offending CEX/ring edge not observed',
        'representative_rewrite':'Full CO literal comparison includes phase; final h literal3058 is renumbering, not evidence of a root/h merge',
    }))
print('Parameter/source and wb diagnostics verified')
