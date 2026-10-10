#!/usr/bin/env python3
"""COMPUTATIONAL: direct gained intersection sums, all threshold costs, root pins.

This checker enumerates complete configurations, not Lean's elimination sums.
Row output gauges set the first incidence permutation to identity; cardinality
costs and every root pin are unchanged by those row relabellings.
"""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import permutations, product
import json
from pathlib import Path
import random


def nested(rows):
    return all(a & b in (a, b) for a in rows for b in rows)


def is_order(rows, order):
    current = rows
    for v in order:
        if not nested(tuple(d for d in current if d >> v & 1)):
            return False
        current = tuple(d & ~(1 << v) for d in current)
    return True


def orders(rows, n):
    return tuple(p for p in permutations(range(n)) if is_order(rows, p))


@lru_cache(None)
def permutation_maps(m):
    return tuple(tuple(sum(1 << p[x] for x in range(m) if d >> x & 1)
                       for d in range(1 << m)) for p in permutations(range(m)))


def normalized_gains(rows, n, m):
    slots = tuple((i, v) for i, d in enumerate(rows)
                  for v in tuple(v for v in range(n) if d >> v & 1)[1:])
    for labels in product(range(len(permutation_maps(m))), repeat=len(slots)):
        g = [[0] * n for _ in rows]
        for (i, v), p in zip(slots, labels):
            g[i][v] = p
        yield tuple(tuple(row) for row in g)


@lru_cache(None)
def threshold_vectors(m, ranks):
    return tuple(product(*(range(r + 1) for r in ranks)))


def table(rows, n, m, gains):
    maps = permutation_maps(m)
    incidences = tuple(tuple((v, maps[gains[i][v]]) for v in range(n) if d >> v & 1)
                       for i, d in enumerate(rows))
    result = Counter()
    for sets in product(range(1 << m), repeat=n):
        sizes = tuple(d.bit_count() for d in sets)
        ranks = []
        for edges in incidences:
            overlap = (1 << m) - 1
            for v, transform in edges:
                overlap &= transform[sets[v]]
            ranks.append(overlap.bit_count())
        for threshold in threshold_vectors(m, tuple(ranks)):
            result[(sizes, -1, 0, threshold)] += 1
            for root in range(n):
                result[(sizes, root, sets[root], threshold)] += 1
    return result


def check_family(rows, n, m, gains, stats):
    oo = orders(rows, n)
    if not oo:
        stats['excluded_non_nest_families'] += 1
        return
    assert n == 0 or {p[-1] for p in oo} == set(range(n))
    stats['nest_families'] += 1
    stats['root_last_order_certificates'] += n
    ordinary = table(rows, n, m, tuple((0,) * n for _ in rows))
    # Every actual identity residual is checked; do not drop a retained root.
    for order in oo:
        for offset, v in enumerate(order):
            residual = tuple(d & ~sum(1 << w for w in order[:offset + 1]) for d in rows)
            assert nested(tuple(d for d, original in zip(residual, rows) if original >> v & 1))
            stats['nested_identity_recovery_steps'] += 1
    for gain in gains:
        gained = table(rows, n, m, gain)
        assert all(value <= ordinary[key] for key, value in gained.items()), (rows, n, m, gain)
        # Union includes every nonzero ordinary cell, so equality and zero
        # gained sums are checked too. Omitted cells have both sides zero.
        keys = ordinary.keys() | gained.keys()
        stats['gain_systems'] += 1
        stats['threshold_cost_comparisons'] += len(keys)
        stats['pinned_comparisons'] += sum(key[1] >= 0 for key in keys)
        stats['zero_gained_cells'] += sum(gained[key] == 0 for key in keys)
        stats['strict_cells'] += sum(gained[key] < ordinary[key] for key in keys)


def controls():
    # One left row and two prescribed right sets: an independent gain can
    # align disjoint pins. This disproves retaining two arbitrary roots.
    row = (3,)
    id_gain = ((0, 0),)
    twist = ((0, 1),)
    q0, q1 = 1, 2
    identity_overlap = q0 & q1
    twisted_overlap = q0 & permutation_maps(2)[1][q1]
    assert identity_overlap.bit_count() == 0 and twisted_overlap.bit_count() == 1
    assert is_order(row, (0, 1))
    # A first nest column alone says nothing about the residual suffix:
    # isolated column 3 followed by the three-cycle incidence rows.
    cyclic = (3, 6, 5)
    assert nested(tuple(d for d in cyclic if d >> 3 & 1))
    assert not orders(cyclic, 3)
    return [
        {'status': 'REFUTED-STRENGTHENING', 'claim': 'Retain two arbitrary right sets.',
         'data': 'K1,2, M=2, Q0={0}, Q1={1}; identity intersection size 0, swapping the second edge gives size 1. The monotone cost F(d)=d increases.'},
        {'status': 'REFUTED-STRENGTHENING', 'claim': 'A first nest point guarantees an elimination order of the suffix.',
         'data': 'Rows {0,1}, {1,2}, {0,2} and isolated column 3: column 3 is a nest point, but the remaining three-column family has no nest point.'}]


def run():
    stats = Counter()
    for m in range(3):
        for s in range(4):
            for n in range(4):
                for rows in product(range(1 << n), repeat=s):
                    check_family(rows, n, m, normalized_gains(rows, n, m), stats)
    for s in range(3):
        for n in range(3):
            for rows in product(range(1 << n), repeat=s):
                check_family(rows, n, 3, normalized_gains(rows, n, 3), stats)
    # Noncommuting S3 systems on every row-gauged K2,3 incidence system.
    check_family((7, 7), 3, 3, normalized_gains((7, 7), 3, 3), stats)
    rng = random.Random(20261010)
    for rows, n, m, count in [((7, 7, 7), 3, 3, 48), ((3, 7, 7), 3, 3, 24), ((7, 7), 3, 4, 16)]:
        gains = []
        for _ in range(count):
            gain = []
            for d in rows:
                first = next((v for v in range(n) if d >> v & 1), None)
                gain.append(tuple(0 if v == first or not d >> v & 1 else rng.randrange(len(permutation_maps(m)))
                                  for v in range(n)))
            gains.append(tuple(gain))
        check_family(rows, n, m, gains, stats)
    return {'status': 'COMPUTATIONAL', 'result': 'PASS', 'counts': dict(stats),
            'scope': 'All M=0..2, 0..3 indexed rows and columns, every set family admitting a full nest order, and every gain system up to row output gauges. Also all M=3 families with up to two rows/columns, all row-gauged S3 systems on K2,3, and seeded larger-gain fixtures. Direct complete-configuration sums compare every threshold-product generator, both unpinned and at every root/set pin. Every omitted table cell is zero in both models.',
            'negative_controls': controls(),
            'role': 'Finite diagnostics only; not a Lean premise or a proof of chordal rigidity or A–C.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(run(), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
