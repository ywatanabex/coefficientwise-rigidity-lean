#!/usr/bin/env python3
"""COMPUTATIONAL: C4 with raw forward-edge counts and all mixed surpluses.

No finite result is imported by Lean. The raw count does not use the
intersection formula or the saturation recurrence. Gain normalization is
only a choice of vertex labels; both saturation orientations are checked.
"""
import argparse
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, product
from math import comb, prod
import json
from pathlib import Path
import random
from check_cone_elimination import normalized_gains, permutation_maps


def chordal(rows, n):
    """Direct induced-cycle prohibition, independently of nest orders."""
    s = len(rows)
    adjacent = [set() for _ in range(s + n)]
    for i, row in enumerate(rows):
        for j in range(n):
            if row >> j & 1:
                adjacent[i].add(s + j)
                adjacent[s + j].add(i)
    for k in range(6, s + n + 1, 2):
        for vertices in combinations(range(s + n), k):
            subset = set(vertices)
            if not all(len(adjacent[v] & subset) == 2 for v in subset):
                continue
            reached = {vertices[0]}
            while True:
                new = reached | set.union(*(adjacent[v] & subset for v in reached))
                if new == reached:
                    break
                reached = new
            if reached == subset:
                return False
    return True


@lru_cache(None)
def inverses(m):
    maps = permutation_maps(m)
    return tuple(maps.index(tuple(p.index(d) for d in range(1 << m))) for p in maps)


def transpose(rows, n, m, gains):
    return (tuple(sum(1 << i for i, row in enumerate(rows) if row >> j & 1) for j in range(n)),
            len(rows), tuple(tuple(inverses(m)[gains[i][j]] for i in range(len(rows))) for j in range(n)))


def raw_counts(rows, n, m, gains):
    """Check every complete selected-set assignment against forward transports."""
    maps = permutation_maps(m)
    edges = [(i, len(rows) + j, maps[gains[i][j]])
             for i, row in enumerate(rows) for j in range(n) if row >> j & 1]
    result = Counter()
    for sets in product(range(1 << m), repeat=len(rows) + n):
        if all(not (p[sets[i]] & sets[j]) for i, j, p in edges):
            result[tuple(d.bit_count() for d in sets)] += 1
    return result


def intersection_histograms(rows, n, m, gains):
    """Available left labels are inverse images of right complements."""
    maps, inv = permutation_maps(m), inverses(m)
    edges = [[(j, maps[inv[gains[i][j]]]) for j in range(n) if row >> j & 1]
             for i, row in enumerate(rows)]
    histograms = defaultdict(Counter)
    for qsets in product(range(1 << m), repeat=n):
        ranks = []
        for incidents in edges:
            available = (1 << m) - 1
            for j, p in incidents:
                available &= p[qsets[j]]
            ranks.append(available.bit_count())
        histograms[tuple(m - q.bit_count() for q in qsets)][tuple(ranks)] += 1
    return histograms


def profile_checks(stats):
    for b in range(1, 21):
        for a in range(1, b + 1):
            c = comb(b - 1, a - 1)
            assert c > 0
            previous = 0
            for d in range(2 * b + 3):
                f, g, h = comb(min(d, b), a), int(d >= b), comb(min(d, b - 1), a)
                assert f == h + c * g and h >= previous
                if d <= b:
                    assert f == comb(d, a) and g == comb(d, b)
                if a == b:
                    assert h == 0 and c == 1
                previous = h
                stats['profile_cells'] += 1


def check_orientation(rows, n, m, gain, original, ordinary, stats):
    s = len(rows)
    hg = intersection_histograms(rows, n, m, gain)
    ho = intersection_histograms(rows, n, m, tuple((0,) * n for _ in rows))
    neighbors = [tuple(j for j in range(n) if row >> j & 1) for row in rows]
    for a in product(range(1, m + 1), repeat=s + n):
        if any(a[i] + a[s + j] > m for i, ns in enumerate(neighbors) for j in ns):
            continue
        cap = tuple(m - max((a[s + j] for j in ns), default=0) for ns in neighbors)
        saturated = cap + a[s:]
        cs = tuple(comb(cap[i] - 1, a[i] - 1) for i in range(s))
        multiplier = prod(cs)
        assert multiplier > 0 and all(a[i] <= cap[i] <= m for i in range(s))
        differences = []
        for t in range(1 << s):
            totals = []
            for hist in (ho[a[s:]], hg[a[s:]]):
                total = 0
                for d, multiplicity in hist.items():
                    assert all(d[i] <= cap[i] for i in range(s))
                    total += multiplicity * prod(int(d[i] >= cap[i]) if t >> i & 1
                                                 else comb(min(d[i], cap[i] - 1), a[i])
                                                 for i in range(s))
                totals.append(total)
            delta = totals[0] - totals[1]
            assert delta >= 0, (rows, n, m, gain, a, t, totals)
            differences.append(delta)
            stats['mixed_nonnegative_terms'] += 1
        deficit = ordinary[a] - original[a]
        saturated_deficit = ordinary[saturated] - original[saturated]
        assert saturated_deficit == differences[-1]
        excess = sum(prod(cs[i] for i in range(s) if t >> i & 1) * differences[t]
                     for t in range((1 << s) - 1))
        assert deficit == multiplier * saturated_deficit + excess
        assert deficit >= multiplier * saturated_deficit >= 0
        if deficit == 0:
            assert saturated_deficit == 0
            stats['zero_deficit_transfers'] += 1
        stats['saturation_identities'] += 1
        stats['strict_surpluses'] += excess > 0
        stats['nontrivial_multipliers'] += multiplier > 1
        stats['isolated_full_rank_profiles'] += any(not rows[i] and a[i] == m for i in range(s))


def check_family(rows, n, m, gains, stats):
    if not chordal(rows, n):
        stats['excluded_nonchordal_families'] += 1
        return
    ordinary = raw_counts(rows, n, m, tuple((0,) * n for _ in rows))
    for gain in gains:
        original = raw_counts(rows, n, m, gain)
        stats['gain_fixtures'] += 1
        stats['raw_assignments_examined'] += (1 << m) ** (len(rows) + n)
        check_orientation(rows, n, m, gain, original, ordinary, stats)
        tr, tn, tg = transpose(rows, n, m, gain)
        tr_original = Counter({a[len(rows):] + a[:len(rows)]: c for a, c in original.items()})
        tr_ordinary = Counter({a[len(rows):] + a[:len(rows)]: c for a, c in ordinary.items()})
        check_orientation(tr, tn, m, tg, tr_original, tr_ordinary, stats)


def negative_control():
    # Dropping positive ranks from saturation is false, even though the original comparison holds.
    rows, n, m, gain = (3, 3), 2, 2, ((0, 0), (0, 1))
    gained = raw_counts(rows, n, m, gain)
    ordinary = raw_counts(rows, n, m, ((0, 0), (0, 0)))
    a, saturated = (0, 0, 1, 1), (1, 1, 1, 1)
    d, ds = ordinary[a] - gained[a], ordinary[saturated] - gained[saturated]
    assert d == 0 and ds == 2
    return {'status': 'REFUTED-STRENGTHENING',
            'claim': 'Saturation transfers zero deficit without positive row occupations.',
            'fixture': 'K2,2, M=2, one transposed edge, a=(0,0,1,1), saturated=(1,1,1,1).',
            'original_deficit': d, 'saturated_deficit': ds,
            'role': 'Does not refute C4, active-support reduction, or Watanabe comparison.'}


def run():
    stats = Counter()
    profile_checks(stats)
    for m in range(3):
        for s in range(4):
            for n in range(4):
                for rows in product(range(1 << n), repeat=s):
                    check_family(rows, n, m, normalized_gains(rows, n, m), stats)
    for s in range(3):
        for n in range(3):
            for rows in product(range(1 << n), repeat=s):
                check_family(rows, n, 3, normalized_gains(rows, n, 3), stats)
    rng = random.Random(20261010)
    for rows, n, m, count in [((7, 7), 3, 3, 12), ((7, 7, 7), 3, 3, 4),
                               ((3, 7, 7), 3, 3, 4), ((7, 7), 3, 4, 8), ((3, 3), 2, 5, 4)]:
        gains = [tuple(tuple(rng.randrange(len(permutation_maps(m))) for _ in range(n))
                       for _ in rows) for _ in range(count)]
        check_family(rows, n, m, gains, stats)
    assert stats['strict_surpluses'] > 0 and stats['nontrivial_multipliers'] > 0
    return {'status': 'COMPUTATIONAL', 'result': 'PASS', 'counts': dict(stats),
            'scope': 'All chordal bipartite graphs with 0..3 vertices per side, M=0..2, all gains up to row vertex gauges; M=3 with 0..2 per side; seeded S3/S4/S5 fixtures. Every positive feasible occupation and both saturation orientations. Raw complete selected-set counts independently check the coefficient identity and every nonnegative mixed term.',
            'negative_controls': [negative_control()],
            'role': 'Finite diagnostics only, never a Lean premise; full A–C remain incomplete.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = run()
    data = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(data)
    print(data, end='')
