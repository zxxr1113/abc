"""Additional unsampled top-eight only; the witnessed baseline is a separate call.
Enumeration and normalized retention accounting mirror the authenticated frozen
prototype. Sentinel rank observation never changes admission or its key.
"""
from collections import Counter
from common import cid, require

def search_unsampled(p, s, row, seq, seq_mask, free, free_mask, config, deadline, sentinels=()):
    root, pool = row['root'], row['pool']
    info = {int(k): v for k, v in row['pool_info'].items()}
    require(config.candidates_per_root == 8, 'fixed frontier cap is eight')
    literals = [(2*n+phase, seq[n] ^ (seq_mask if phase else 0)) for n in pool for phase in (0, 1)]
    pairs = [(a, b, sa & sb) for j, (a, sa) in enumerate(literals)
             for b, sb in literals[j+1:] if a != (b ^ 1)]
    mffc = s.mffc(root)
    positions = {n: bit for bit, n in enumerate(sorted(mffc))}
    protected_masks, seen, found = {}, set(), {}
    stats = Counter()
    # Rank observers contain only three predetermined identities; their costs
    # are computed using the same cost function, not used to alter the frontier.
    observers = {}
    for ident in sentinels:
        if ident[0] == root:
            recipe, out = list(ident[1]), ident[2]
            norm = p.normalize(s, root, recipe, out)
            require(norm == (recipe, out), 'sentinel is not normalized')
            cost = s.cost(root, recipe, out)
            observers[ident] = dict(key=p.candidate_key(dict(recipe=recipe, out=out, **cost)),
                                   earlier=0, found=False)
    def protected(n):
        if n not in protected_masks:
            protected_masks[n] = sum(1 << positions[x] for x in s.tfi([n], mffc))
        return protected_masks[n]
    def accept(recipe, out):
        stats['signature_hits'] += 1
        recipe, out = p.normalize(s, root, recipe, out)
        if not recipe:
            stats['direct_after_hash'] += 1
            return
        ident = (root, tuple(recipe), out)
        if ident in seen:
            return
        seen.add(ident)
        require(p.recipe_eval(recipe, out, seq, seq_mask) == seq[root], 'normalization changed sequence match')
        if p.recipe_eval(recipe, out, free, free_mask) ^ free[root]:
            stats['witnessed_excluded'] += 1
            return
        stats['no_sampled_free_witness'] += 1
        used = sorted(p.external_nodes(recipe, out))
        require(all(0 < n < root for n in used), 'illegal/cyclic divisor')
        keep = 0
        for n in used:
            keep |= protected(n)
        fresh = len(recipe)//2
        gain = len(mffc)-keep.bit_count()-fresh
        if gain <= 0:
            stats['nonpositive_retention_gain'] += 1
            return
        if not any(n > s.nci for n in used):
            stats['ci_only_recipe'] += 1
            return
        stats['positive_unsampled_candidates'] += 1
        key = (-gain, fresh, recipe, out)
        for observed, data in observers.items():
            data['earlier'] += key < data['key']
            data['found'] |= ident == observed
        cost = dict(original_mffc=len(mffc),
                    retained_mffc_nodes=[n for n, bit in positions.items() if keep >> bit & 1],
                    removable_nodes=[n for n, bit in positions.items() if not (keep >> bit & 1)],
                    removable=len(mffc)-keep.bit_count(), fresh_gates=fresh, conservative_gain=gain)
        roles = {str(n): info.get(n, dict(roles=['hash_reuse'], nonlinear=n > s.nci)) for n in used}
        candidate = dict(root=root, recipe=recipe, out=out, divisors=used, divisor_roles=roles,
                         discovery_domain='initial256_unsampled_difference', **cost)
        found[ident] = candidate
        if len(found) > 8:
            del found[max(found, key=lambda x: p.candidate_key(found[x]))]
    for a, b, signature in pairs:
        deadline.remaining()
        if signature == seq[root]:
            accept([a, b], -2)
        if signature ^ seq_mask == seq[root]:
            accept([a, b], -3)
    if config.max_gates == 2:
        for output_phase in (0, 1):
            target = seq[root] ^ (seq_mask if output_phase else 0)
            for c, sc in literals:
                deadline.remaining()
                if target & (sc ^ seq_mask):
                    continue
                for index, (a, b, first) in enumerate(pairs):
                    if index % 128 == 0:
                        deadline.remaining()
                    if first & sc == target:
                        accept([a, b, -2, c], -(4+output_phase))
                    if (first ^ seq_mask) & sc == target:
                        accept([a, b, -3, c], -(4+output_phase))
    ordered = sorted(found.values(), key=p.candidate_key)
    stats['candidate_cap_dropped'] = stats['positive_unsampled_candidates']-len(ordered)
    for c in ordered:
        require(all(c[k] == v for k, v in s.cost(root, c['recipe'], c['out']).items()),
                'retention mask differs from independent reference count')
    ranks = [dict(candidate_id=[i[0], list(i[1]), i[2]], eligible=v['found'],
                  rank=v['earlier']+1 if v['found'] else None, retained=i in found,
                  injected=False) for i, v in observers.items()]
    return ordered, dict(stats), ranks
