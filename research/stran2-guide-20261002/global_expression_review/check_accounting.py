#!/usr/bin/env python3
"""Read-only confirmation of the saved wb demotion and corrected aggregates."""
import json
from pathlib import Path

from review import Aig, digest


def load(path):
    return json.loads(Path(path).read_text())


def main():
    root = Path('/tmp/nonlinear-anytime-v2-global-alias-audit-v1/060_wb_dma')
    comparison_path = Path('/tmp/image-guided-global-corrected-comparison.json')
    result = load(root / 'result.json')
    old = Path('/tmp/nonlinear-anytime-pilot-v2/060_wb_dma')
    old_result = load(old / 'result.json')
    checkpoint = Path(old_result['selected_checkpoint']['directory'])
    original_selected = load(checkpoint / 'selection.json')['selected']
    assert len(original_selected) == 1
    c = original_selected[0]
    assert (c['root'], c['recipe'], c['out']) == (759, [1144, 1508], -2)
    assert digest(root / 'input.aig') == result['input_sha256'] == old_result['input_sha256']
    old_product_hash = digest(checkpoint / 'product.aig')
    old_product = Aig(checkpoint / 'product.aig')
    assert old_product.m - old_product.nci == 3701
    checked = {}
    abc_hashes = {}
    for lane in ('original', 'mixed'):
        sets = load(root / lane / 'selected_sets.json')
        assert sets['genuinely_new_builds'] == []
        for key in ('original_selected', 'global_existing_output_demotions', 'without_genuinely_new_build'):
            assert sets[key] == original_selected, (lane, key)
        saved = []
        for arm in ('full', 'without_genuinely_new_build'):
            arm_dir = root / lane / arm
            selection = load(arm_dir / 'selection.json')
            assert selection['selected'] == original_selected
            saved.append(selection)
            product_hash = digest(arm_dir / 'product.aig')
            assert product_hash == old_product_hash
            graph = Aig(arm_dir / 'product.aig')
            count = graph.m - graph.nci
            assert count == 3701
            summary = result['products'][lane][arm]
            assert summary['and_count'] == count and summary['sha256'] == product_hash
            certificate = summary['dsec']
            assert certificate['status'] == 'PASS' and certificate['reused_exact_graph_dsec']
            assert digest(certificate['reused_log']) == certificate['log_sha256']
            abc = certificate['abc']
            if abc not in abc_hashes:
                abc_hashes[abc] = digest(abc)
            assert abc_hashes[abc] == certificate['abc_sha256']
        assert saved[0] == saved[1], 'even realization metadata must remain identical'
        assert digest(root / lane / 'full_replay.aig') == old_product_hash
        assert result['products'][lane]['exact_same_selected_set_global_hash_corrected_build_marginal'] == 0
        checked[lane] = dict(selected_root=759, recipe=[1144, 1508], out=-2,
                             original_candidate_object_unchanged_in_full_and_ablation=True,
                             selection_and_realization_objects_identical=True,
                             full_and=3701, ablated_and=3701, exact_build_marginal=0,
                             product_sha256=old_product_hash,
                             historical_graph_and_dsec_bindings_rechecked=True)

    comparison = load(comparison_path)
    cases = comparison['cases']
    for case in cases:
        for field, run in [('baseline_gain', '/tmp/nonlinear-anytime-v2-global-alias-audit-v1'),
                           ('refined_gain', '/tmp/image-guided-global-alias-audit-v1')]:
            row = load(Path(run) / case['case'] / 'result.json')
            assert row['global_hash_corrected_conditional_build_marginal'] == case[field]
            assert row['loaded_and'] == case['loaded_and']
        assert case['delta_gain'] == case['refined_gain'] - case['baseline_gain']

    def check_group(name, group):
        expected = comparison[name]
        assert expected['cases'] == len(group)
        for side in ('baseline', 'refined', 'delta'):
            total = sum(c[side + '_gain'] for c in group)
            equal = 100 * sum(c[side + '_gain'] / c['loaded_and'] for c in group) / len(group)
            weighted = 100 * total / sum(c['loaded_and'] for c in group)
            assert expected[side]['and_gain'] == total
            assert abs(expected[side]['equal_case_percent'] - equal) < 1e-12
            assert abs(expected[side]['weighted_percent'] - weighted) < 1e-12

    assert max(cases, key=lambda c: c['delta_gain'])['case'] == comparison['excluding_largest_increment_case'] == '060_wb_dma'
    check_group('all_cases', cases)
    check_group('excluding_largest_increment', [c for c in cases if c['case'] != '060_wb_dma'])
    check_group('excluding_b03', [c for c in cases if c['case'] != '005_b03'])
    report = dict(status='PASS', script_sha256=digest(__file__), checked_products=checked,
                  original_product_and_reduction=3703 - 3701,
                  original_product_reduction_is_existing_expression_not_new_build=True,
                  comparison_path=str(comparison_path), comparison_sha256=digest(comparison_path),
                  all_three_reported_aggregate_groups_recomputed=True,
                  corrected_all_cases=comparison['all_cases'],
                  new_sat_dsec_or_search_calls=0)
    Path(__file__).with_name('accounting_check.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
