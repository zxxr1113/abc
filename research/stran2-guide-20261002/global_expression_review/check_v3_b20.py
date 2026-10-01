#!/usr/bin/env python3
"""Independent read-only whole-original classification of V3 retry b20."""
import argparse
import json
from pathlib import Path

from review import Aig, audit_selection, digest, selftest


def selected(run):
    result_file = run / '034_b20_opt/result.json'
    result = json.loads(result_file.read_text())
    selection_file = Path(result['selected_checkpoint']['directory']) / 'selection.json'
    return result, selection_file, json.loads(selection_file.read_text())['selected']


def identity(candidate):
    return candidate['root'], tuple(candidate['recipe']), candidate['out']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, default=Path('/workspace/scratch/7e0c7273599c/evidence-preserved/image-guided-pilot-v3-retry1'))
    parser.add_argument('--previous-run', type=Path, default=Path('/tmp/image-guided-pilot-v1'))
    parser.add_argument('--attribution', type=Path, default=Path('/workspace/scratch/7e0c7273599c/evidence-preserved/image-guided-v3-b20-attribution/034_b20_opt'))
    parser.add_argument('--global-audit', type=Path, default=Path('/workspace/scratch/7e0c7273599c/evidence-preserved/image-guided-v3-b20-global-alias/034_b20_opt'))
    parser.add_argument('--out', type=Path, default=Path(__file__).with_name('v3_b20_review.json'))
    args = parser.parse_args()
    result, selection_file, candidates = selected(args.run)
    previous, previous_selection_file, previous_candidates = selected(args.previous_run)
    input_file = Path(__file__).resolve().parents[1] / 'inputs/first_seq/034_b20_opt.aig'
    assert digest(input_file) == result['input_sha256'] == previous['input_sha256']
    checked = audit_selection(Aig(input_file), candidates)
    before, after = {identity(c) for c in previous_candidates}, {identity(c) for c in candidates}
    report = dict(status='PASS', script_sha256=digest(__file__), classifier_sha256=digest(Path(__file__).with_name('review.py')),
                  selftest=selftest(), input_sha256=digest(input_file), input_file=str(input_file),
                  source_selection=str(selection_file), source_selection_sha256=digest(selection_file),
                  previous_selection=str(previous_selection_file), previous_selection_sha256=digest(previous_selection_file),
                  previous_selected_count=len(before), current_selected_count=len(after),
                  retained_previous_recipe_identities=len(before & after),
                  added_recipe_identities=sorted(after - before), removed_recipe_identities=sorted(before - after),
                  raw_product_and_reduction=result['product']['exact_same_selected_set_build_gain'],
                  historical_raw_product_and_reduction=previous['product']['exact_same_selected_set_build_gain'],
                  current_search_complete=result['search_complete'],
                  classification=checked,
                  limits='Whole-original structural novelty only; not Boolean novelty, unrestricted Direct saturation, native novelty, or an independently proved exact post-Direct marginal.',
                  new_sat_dsec_or_search_calls=0)
    if (args.attribution / 'result.json').exists() and (args.global_audit / 'result.json').exists():
        attr = json.loads((args.attribution / 'result.json').read_text())
        glob = json.loads((args.global_audit / 'result.json').read_text())
        assert attr['input_sha256'] == glob['input_sha256'] == result['input_sha256']
        assert attr['proved_positive_directs'] == 0
        assert attr['exact_same_mixed_selected_set_build_marginal'] == 75
        assert glob['global_hash_corrected_conditional_build_marginal'] == 75
        checked_graphs = []
        for lane in ('original', 'mixed'):
            sets = json.loads((args.global_audit / lane / 'selected_sets.json').read_text())
            assert sets['global_existing_output_demotions'] == []
            assert sets['original_selected'] == sets['genuinely_new_builds'] == candidates
            assert sets['without_genuinely_new_build'] == []
            for arm, expected_candidates, expected_count, expected_hash in (
                    ('full', candidates, 11195, result['product']['product_sha256']),
                    ('without_genuinely_new_build', [], 11270, result['product']['replay_without_build_sha256'])):
                folder = args.global_audit / lane / arm
                selection = json.loads((folder / 'selection.json').read_text())
                assert selection['selected'] == expected_candidates
                graph = Aig(folder / 'product.aig')
                assert graph.m - graph.nci == expected_count
                assert digest(folder / 'product.aig') == expected_hash
                certificate = glob['products'][lane][arm]['dsec']
                assert certificate['status'] == 'PASS' and certificate['reused_exact_graph_dsec']
                assert digest(certificate['reused_log']) == certificate['log_sha256']
                checked_graphs.append(dict(lane=lane, arm=arm, and_count=expected_count,
                                           selected_count=len(expected_candidates), sha256=expected_hash))
        for arm, expected_count, expected_candidates, expected_hash in (
                ('mixed', 11195, candidates, result['product']['product_sha256']),
                ('same_mixed_set_without_build', 11270, [], result['product']['replay_without_build_sha256']),
                ('direct_only', 11270, [], result['product']['replay_without_build_sha256'])):
            folder = args.attribution / arm
            assert json.loads((folder / 'selection.json').read_text())['selected'] == expected_candidates
            graph = Aig(folder / 'product.aig')
            assert graph.m - graph.nci == expected_count
            assert digest(folder / 'product.aig') == expected_hash
        report['accounting_artifact_check'] = dict(status='PASS', checked_graphs=checked_graphs,
                                                   conditional_build_marginal=11270 - 11195,
                                                   full_selection_matches_raw_checkpoint=True,
                                                   ablated_selection_empty=True,
                                                   attribution_graphs_and_selections_match_global_audit=True,
                                                   direct_proofs_status='0 positive Direct proofs recorded within bounded audit; not independently rerun',
                                                   audit_result_sha256=digest(args.attribution / 'result.json'),
                                                   global_result_sha256=digest(args.global_audit / 'result.json'))
        report['limits'] = 'Whole-original structural novelty and exact saved post-Direct marginal verified; not Boolean novelty, unrestricted Direct saturation, or native novelty. No independent rerun of formal proofs.'
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('classification', 'added_recipe_identities', 'removed_recipe_identities')}, indent=2))
    print(json.dumps(checked['counts']))


if __name__ == '__main__':
    main()
