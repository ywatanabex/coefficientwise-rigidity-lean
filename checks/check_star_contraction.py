#!/usr/bin/env python3
"""COMPUTATIONAL: exact tight-star maps, parallel labels, gauges and graph class.

Raw configuration enumeration and BFS gauge consistency are independent of
Lean's bijection proofs. Every original edge label survives unless incident
to the deleted centre. Finite diagnostics are never proof premises.
"""
import argparse
from collections import Counter, defaultdict
from itertools import product
import json
from pathlib import Path
import random
from check_cone_elimination import normalized_gains, permutation_maps
from check_saturation import chordal, inverses


def edges_of(rows, n, m, gains):
    maps = permutation_maps(m)
    return [(i, len(rows) + j, maps[gains[i][j]])
            for i, row in enumerate(rows) for j in range(n) if row >> j & 1]


def configurations(vertices, m, edges):
    by_rank = defaultdict(set)
    for sets in product(range(1 << m), repeat=vertices):
        if all(not (p[sets[x]] & sets[y]) for x, y, p in edges):
            by_rank[tuple(s.bit_count() for s in sets)].add(sets)
    return by_rank


def flat(vertices, m, edges):
    """Transport singleton labels along edges, checking every parallel edge."""
    adjacency = [[] for _ in range(vertices)]
    for x, y, mapping in edges:
        p = tuple((mapping[1 << i]).bit_length() - 1 for i in range(m))
        inv = tuple(p.index(i) for i in range(m))
        adjacency[x].append((y, p))
        adjacency[y].append((x, inv))
    gauge = {}
    for root in range(vertices):
        if root in gauge:
            continue
        gauge[root] = tuple(range(m))
        stack = [root]
        while stack:
            x = stack.pop()
            for y, p in adjacency[x]:
                candidate = tuple(p[i] for i in gauge[x])
                if y in gauge:
                    if gauge[y] != candidate:
                        return False
                else:
                    gauge[y] = candidate
                    stack.append(y)
    return True


def contraction(rows, n, m, gains, u):
    s = len(rows)
    neighbours = tuple(s + j for j in range(n) if rows[u] >> j & 1)
    outside = tuple(v for v in range(s + n) if v != u and v not in neighbours)
    z = len(outside)
    projection = {v: i for i, v in enumerate(outside)}
    projection.update({v: z for v in neighbours + (u,)})
    maps = permutation_maps(m)
    identity = maps[0]
    gauge = [identity for _ in range(s + n)]
    ungauge = [identity for _ in range(s + n)]
    for v in neighbours:
        ungauge[v] = maps[gains[u][v - s]]
        gauge[v] = maps[inverses(m)[gains[u][v - s]]]
    reduced = []
    for x, y, p in edges_of(rows, n, m, gains):
        if x == u:
            continue
        # Star gauges act only at right neighbours; all left gauges are identity.
        transformed = tuple(gauge[y][p[d]] for d in range(1 << m))
        reduced.append((projection[x], projection[y], transformed))
    rrows = tuple(sum(1 << (j - (s - 1)) for j in {y for x, y, _ in reduced if x == i})
                  for i in range(s - 1))
    return outside, z, projection, gauge, ungauge, reduced, rrows, n - len(neighbours) + 1


def structural_checks(stats):
    for s in range(1, 4):
        for n in range(5):
            for rows in product(range(1 << n), repeat=s):
                if not chordal(rows, n):
                    continue
                stats['chordal_graphs'] += 1
                identity = tuple((0,) * n for _ in rows)
                for u in range(s):
                    outside, z, pi, _, _, edges, rr, rn = contraction(rows, n, 1, identity, u)
                    assert len(outside) + 1 == s + n - rows[u].bit_count()
                    assert chordal(rr, rn), (rows, n, u, rr, rn)
                    assert all(x != y for x, y, _ in edges)
                    assert len(edges) == sum(row.bit_count() for row in rows) - rows[u].bit_count()
                    assert all(pi[s + j] == z for j in range(n) if rows[u] >> j & 1)
                    stats['structural_contractions'] += 1
                    stats['strict_size_decreases'] += bool(rows[u])
                    stats['parallel_edge_instances'] += len(edges) - len({(x, y) for x, y, _ in edges})


def check_family(rows, n, m, gains, stats):
    if not chordal(rows, n):
        return
    s = len(rows)
    full = (1 << m) - 1
    identity = tuple((0,) * n for _ in rows)
    original_ordinary = configurations(s + n, m, edges_of(rows, n, m, identity))
    for a in product(range(m + 1), repeat=s + n):
        feasible = all(a[i] + a[s + j] <= m for i, row in enumerate(rows)
                       for j in range(n) if row >> j & 1)
        assert (a in original_ordinary) == feasible
    for gain in gains:
        edges = edges_of(rows, n, m, gain)
        original = configurations(s + n, m, edges)
        original_flat = flat(s + n, m, edges)
        stats['gain_fixtures'] += 1
        stats['raw_gained_assignments'] += (1 << m) ** (s + n)
        for u in range(s):
            outside, z, pi, gauge, ungauge, reduced_edges, rr, rn = contraction(rows, n, m, gain, u)
            reduced = configurations(z + 1, m, reduced_edges)
            reduced_ordinary = configurations(z + 1, m,
                                              [(x, y, permutation_maps(m)[0]) for x, y, _ in reduced_edges])
            assert flat(z + 1, m, reduced_edges) == original_flat
            stats['flatness_equivalences'] += 1
            for a, ordinary_configs in original_ordinary.items():
                if any(a[s + j] != m - a[u] for j in range(n) if rows[u] >> j & 1):
                    continue
                ar = tuple(a[v] for v in outside) + (m - a[u],)
                assert len(ordinary_configs) == len(reduced_ordinary[ar])
                assert all(ar[x] + ar[y] <= m for x, y, _ in reduced_edges)
                image = set()
                for selected in original[a]:
                    normalized = tuple(gauge[v][selected[v]] for v in range(s + n))
                    contracted = tuple(normalized[v] for v in outside) + (full ^ normalized[u],)
                    assert all(normalized[s + j] == contracted[z] for j in range(n) if rows[u] >> j & 1)
                    assert contracted not in image
                    image.add(contracted)
                    lifted = tuple(full ^ contracted[z] if v == u else contracted[pi[v]] for v in range(s + n))
                    restored = tuple(ungauge[v][lifted[v]] for v in range(s + n))
                    assert restored == selected
                    stats['configuration_round_trips'] += 1
                assert image == reduced[ar], (rows, n, m, gain, u, a)
                stats['exact_coefficient_pairs'] += 1
                stats['zero_gained_pairs'] += not image
                stats['isolated_centres'] += not rows[u]
                stats['zero_or_full_rank_profiles'] += any(v in (0, m) for v in a)
            # This separately checks the C4 input that supplies a tight maximal star.
            for a in original_ordinary:
                if not all(a) or a[u] != max(a[:s]) or not rows[u]:
                    continue
                saturated = a[:s] + tuple(m - max((a[i] for i, row in enumerate(rows) if row >> j & 1), default=0)
                                          for j in range(n))
                assert all(saturated[s + j] == m - a[u] for j in range(n) if rows[u] >> j & 1)
                ar = tuple(saturated[v] for v in outside) + (m - saturated[u],)
                assert all(0 < x <= m for x in ar)
                stats['positive_maximal_saturation_instances'] += 1


def parallel_control():
    rows, n, m, gain = (3, 3), 2, 2, ((0, 0), (0, 1))
    outside, z, _, _, _, edges, _, _ = contraction(rows, n, m, gain, 0)
    assert len(edges) == 2 and edges[0][:2] == edges[1][:2]
    full = configurations(z + 1, m, edges)
    representative = configurations(z + 1, m, edges[:1])
    assert not flat(z + 1, m, edges) and flat(z + 1, m, edges[:1])
    assert len(full[(1, 1)]) == 0 and len(representative[(1, 1)]) == 2
    return {'status': 'REFUTED-STRENGTHENING',
            'claim': 'Discarding all but one parallel edge preserves counts or flatness.',
            'fixture': 'K2,2, M=2, one swapped edge, contract a normalized left star.',
            'full_labelled_count': 0, 'simple_representative_count': 2,
            'full_flat': False, 'representative_flat': True,
            'role': 'C5 must preserve both labels; C6 must account for the rejected configurations.'}


def run():
    stats = Counter()
    structural_checks(stats)
    for m in range(3):
        for s in range(1, 4):
            for n in range(4):
                if s == 3 and n == 3:
                    continue
                for rows in product(range(1 << n), repeat=s):
                    check_family(rows, n, m, normalized_gains(rows, n, m), stats)
    for s in range(1, 3):
        for n in range(3):
            for rows in product(range(1 << n), repeat=s):
                check_family(rows, n, 3, normalized_gains(rows, n, 3), stats)
    rng = random.Random(20261011)
    for rows, n, m, count in [((7, 7, 7), 3, 2, 12), ((7, 7, 7), 3, 3, 4),
                               ((3, 7, 7), 3, 3, 4), ((7, 7), 3, 3, 12), ((3, 3), 2, 4, 4)]:
        gains = [tuple(tuple(rng.randrange(len(permutation_maps(m))) for _ in range(n))
                       for _ in rows) for _ in range(count)]
        check_family(rows, n, m, gains, stats)
    return {'status': 'COMPUTATIONAL', 'result': 'PASS', 'counts': dict(stats),
            'scope': 'Graph class and exact size: every chordal bipartite graph with 1..3 left and 0..4 right vertices, every left centre. Exact configuration maps/counts and BFS flatness: all M=0..2 graphs with 1..3 left and 0..3 right except 3-by-3, all gains up to row vertex gauges; M=3 up to 2-by-2; seeded S2/S3/S4 fixtures. All feasible tight occupations, including zero/full ranks, plus positive maximal-star saturation inputs.',
            'negative_controls': [parallel_control()],
            'role': 'Finite diagnostics only, never a Lean premise; C6 and full A–C are still incomplete.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = run()
    data = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(data)
    print(data, end='')
