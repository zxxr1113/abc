#!/usr/bin/env python3
"""Export reviewed final graph pairs/logs, not full raw SAT/model certificates."""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import shutil
import tarfile

ARMS=('inline_free_off','predecessor_cache_off','predecessor_cache_on')
def read(path):return json.loads(Path(path).read_text())
def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb')as f:
        for row in iter(lambda:f.read(1024*1024),b''):h.update(row)
    return h.hexdigest()
def export(run,out,packet,review,review_sha):
    run=run.resolve();out=out.resolve();review=review.resolve();packet=packet.resolve()
    assert not out.exists()and not out.is_relative_to(run)
    assert sha(review)==review_sha,'explicit independent review binding changed'
    reviewed=read(review)
    assert reviewed['status']in('PASS','INDEPENDENT_REVIEW_PASS','PASS_ALL18_FRESH_ARM_PROOF_PRODUCT_PROVENANCE_ACCOUNTING'),'independent PASS required'
    execution=read(run/'execution.json');assert execution['status']=='FINISHED'and execution['validated']==18
    plan=read(run/'plan.json');assert sha(run/'plan.json')==execution['plan_sha256']
    assert reviewed['plan_sha256']==execution['plan_sha256'],'review refers to another plan'
    out.mkdir(parents=True);copies=[];pairs=[]
    def copy(source,relative,expected=None):
        relative=Path(relative);assert not relative.is_absolute()and '..'not in relative.parts
        source=Path(source).resolve();before=sha(source)
        if expected is not None:assert before==expected,'source binding mismatch: '+str(source)
        destination=out/relative;destination.parent.mkdir(parents=True,exist_ok=True)
        assert not destination.exists();shutil.copy2(source,destination)
        assert sha(source)==sha(destination)==before,'copy or source changed'
        copies.append(dict(file=str(relative),sha256=before,bytes=destination.stat().st_size,original_source=str(source)))
        return str(relative)
    for name in ('plan.json','approval_gate.json','execution.json','summary.json'):
        copy(run/name,Path('evidence')/name)
    copy(packet,'evidence/compact_packet.json');copy(review,'evidence/independent_review.json',review_sha)
    index=read(review.parent/'index.json')
    copy(review.parent/'index.json','evidence/reviews/index.json')
    for name,binding in index['files'].items():
        copy(review.parent/name,Path('evidence/reviews')/name,binding['sha256'])
    for case in plan['cases']:
        stem=Path(case['file']).stem
        copy(run/'source'/case['first_seq_path'],Path('inputs/first_seq')/case['file'],case['first_seq_sha256'])
        copy(run/'source'/case['loaded_path'],Path('inputs/loaded')/case['file'],case['loaded_sha256'])
        for arm in ARMS:
            base=run/'audits'/stem/arm/'global'/stem;result=read(base/'result.json');mixed=result['products']['mixed']
            relative=Path('products')/stem/arm;pair=dict(case=case['file'],arm=arm,
                genuine_build_and=result['global_hash_corrected_conditional_build_marginal'],
                input_file=str(Path('inputs/first_seq')/case['file']),input_sha256=case['first_seq_sha256'],graphs={})
            for role,label in [('full','selected'),('without_genuinely_new_build','same_set_without_genuine_build')]:
                graph=mixed[role];receipt=graph['dsec'];assert receipt['status']=='PASS'and receipt['exit_code']==0
                command=shlex.split(receipt['command']);assert len(command)==3 and command[0]=='dsec'
                original_input=Path(command[1]).resolve();original_graph=Path(command[2]).resolve()
                assert original_input.is_relative_to(run)and original_graph.is_relative_to(run),'no historical other-run graph reuse'
                assert sha(original_input)==case['first_seq_sha256']and sha(original_graph)==graph['sha256']
                log=Path(receipt['reused_log']).resolve();assert log.is_relative_to(run)
                graph_file=copy(original_graph,relative/(label+'.aig'),graph['sha256'])
                log_file=copy(log,relative/(label+'.dsec.log'),receipt['log_sha256'])
                pair['graphs'][role]=dict(file=graph_file,sha256=graph['sha256'],and_count=graph['and_count'],
                    dsec_log=log_file,dsec_log_sha256=receipt['log_sha256'],original_dsec_receipt=receipt,
                    portability_note='Original command/log retained verbatim; this relative mapping points to byte-identical exported inputs and graphs.')
            assert pair['graphs']['without_genuinely_new_build']['and_count']-pair['graphs']['full']['and_count']==pair['genuine_build_and']
            for name in ('result.json','classification.json','selected_sets.json'):
                copy(base/'mixed'/name,relative/name)
            pairs.append(pair)
    manifest=dict(schema=1,scope='Compact independently reviewed evidence and18 final selected/same-set-ablation graph pairs, with exact graph-bound DSEC logs and six first_seq/loaded inputs. Not all raw SAT/model logs; not a self-contained replay of every proof certificate.',
        original_run=str(run),plan_sha256=execution['plan_sha256'],independent_review_sha256=review_sha,
        no_new_solver_or_graph_rebuild=True,copied_files=copies,arms=pairs,exporter_sha256=sha(__file__))
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    (out/'README.txt').write_text('STRAN2 three-arm final-products export\n\n'+manifest['scope']+'\n\n'
        'Products use the same-run whole-original-alias corrected mixed selection. Removing genuine Build keeps the exact other selected candidates. '
        'DSEC logs may be exact-graph reused within that same run; their original paths remain unchanged in metadata. '
        'manifest.json supplies portable relative paths and SHA256 bindings. No new solver, DSEC, search, or graph reconstruction was run for this export. '
        'The frozen raw run remains separate in scratch. Historical shared-storage runs are not included.\n')
    archive=out.with_name(out.name+'.tar.gz');assert not archive.exists()
    with tarfile.open(archive,'w:gz')as tar:tar.add(out,arcname=out.name)
    assert archive.stat().st_size<18*1024**2,'export exceeds agreed single-archive limit; do not split automatically'
    return dict(directory=str(out),archive=str(archive),archive_bytes=archive.stat().st_size,archive_sha256=sha(archive),
                files=len(copies)+2,graph_pairs=len(pairs),copied_bytes=sum(r['bytes']for r in copies))
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in('run','out','packet','review'):parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--expected-review-sha256',required=True);args=parser.parse_args()
    print(json.dumps(export(args.run,args.out,args.packet,args.review,args.expected_review_sha256),indent=2))
