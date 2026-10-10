#!/usr/bin/env python3
"""COMPUTATIONAL: direct copy graphs, bags, configuration powers and atom fibres.

Independently written local checker. No Lean result is assumed in these
finite diagnostics, and these diagnostics are not used by any Lean proof.
"""
import argparse
from collections import Counter
from itertools import combinations, product
import json
from math import comb
from pathlib import Path
from check_cone_elimination import normalized_gains, permutation_maps
from check_saturation import chordal
from check_star_contraction import configurations, edges_of


def copy_graph(vertices, seam, edges, k):
    """The empty family still retains the induced boundary graph."""
    nodes = [('shared', v) for v in seam]
    nodes += [(i, v) for i in range(k) for v in range(vertices) if v not in seam]
    pos = {node: j for j, node in enumerate(nodes)}
    base = tuple(v for _, v in nodes)
    copied = {}
    for x, y, p in edges:
        if x in seam and y in seam:
            copied[pos['shared', x], pos['shared', y]] = p
        else:
            for i in range(k):
                u = pos['shared' if x in seam else i, x]
                v = pos['shared' if y in seam else i, y]
                copied[u, v] = p
    return nodes, base, [(x, y, p) for (x, y), p in copied.items()]


def direct_counts(vertices, m, edges):
    """Enumerate actual assignments, pruning conflicts as soon as both ends are chosen."""
    previous = [[] for _ in range(vertices)]
    for x, y, p in edges:
        previous[max(x, y)].append((min(x, y), p, x > y))
    selected = [0] * vertices
    ranks = [0] * vertices
    result = Counter()

    def visit(v):
        if v == vertices:
            result[tuple(ranks)] += 1
            return
        for mask in range(1 << m):
            if all(not (p[mask] & selected[u] if forward else p[selected[u]] & mask)
                   for u, p, forward in previous[v]):
                selected[v], ranks[v] = mask, mask.bit_count()
                visit(v + 1)

    visit(0)
    if vertices <= 4:
        brute = configurations(vertices, m, edges)
        assert result == {a: len(cc) for a, cc in brute.items()}
    return result


def is_chordal_bipartite(vertices, left, edges):
    right = sorted(set(range(vertices)) - set(left))
    index = {v: j for j, v in enumerate(right)}
    rows = tuple(sum(1 << index[y] for x, y, _ in edges if x == u) for u in sorted(left))
    return chordal(rows, len(right))


def tree_bags(vertices, edges):
    """Construct a decomposition by exact degree <=2 elimination, or return None."""
    adjacency = {v: set() for v in range(vertices)}
    for x, y, _ in edges:
        adjacency[x].add(y)
        adjacency[y].add(x)

    def eliminate(graph):
        if not graph:
            return [set()], []
        choices = [v for v in graph if len(graph[v]) <= 2]
        if not choices:
            return None
        v = choices[0]
        neighbours = graph[v]
        reduced = {u: ns - {v} for u, ns in graph.items() if u != v}
        for u, w in combinations(neighbours, 2):
            reduced[u].add(w)
            reduced[w].add(u)
        result = eliminate(reduced)
        if result is None:
            return None
        bags, tree = result
        root = next(i for i, bag in enumerate(bags) if neighbours <= bag)
        tree.append((root, len(bags)))
        bags.append(neighbours | {v})
        return bags, tree

    return eliminate(adjacency)


def check_bags(vertices, edges, bags, tree):
    assert all(len(b) <= 3 for b in bags)
    assert set.union(set(), *bags) == set(range(vertices))
    assert all(any({x, y} <= bag for bag in bags) for x, y, _ in edges)
    assert len(tree) == len(bags) - 1
    adj = [set() for _ in bags]
    for x, y in tree:
        adj[x].add(y)
        adj[y].add(x)

    def connected(subset):
        if not subset:
            return True
        reached, pending = set(), [next(iter(subset))]
        while pending:
            u = pending.pop()
            if u not in reached:
                reached.add(u)
                pending.extend((adj[u] & subset) - reached)
        return reached == subset

    assert connected(set(range(len(bags))))
    assert all(connected({i for i, bag in enumerate(bags) if v in bag}) for v in range(vertices))


def copied_bags(nodes, seam, k, bags, tree):
    root = next(t for t, bag in enumerate(bags) if set(seam) <= bag)
    pos = {node: j for j, node in enumerate(nodes)}
    result = [{pos['shared', v] for v in seam}]
    result += [{pos['shared' if v in seam else i, v] for v in bag}
               for i in range(k) for bag in bags]
    index = lambda i, t: 1 + i * len(bags) + t
    result_tree = [(0, index(i, root)) for i in range(k)]
    result_tree += [(index(i, x), index(i, y)) for i in range(k) for x, y in tree]
    return result, result_tree


def structural(stats):
    for s in range(4):
        for n in range(4):
            if s + n > 5:
                continue
            for rows in product(range(1 << n), repeat=s):
                edges = edges_of(rows, n, 1, tuple((0,) * n for _ in rows))
                decomposition = tree_bags(s + n, edges)
                assert decomposition is not None  # At most five bipartite vertices.
                check_bags(s + n, edges, *decomposition)
                seams = [()] + [(v,) for v in range(s + n)] + [(x, y) for x, y, _ in edges]
                for seam in seams:
                    for k in range(4):
                        nodes, base, copied = copy_graph(s + n, seam, edges, k)
                        check_bags(len(nodes), copied, *copied_bags(nodes, seam, k, *decomposition))
                        stats['copied_tree_decompositions'] += 1
                        # Cycle enumeration at most 10 vertices keeps this diagnostic bounded.
                        if len(nodes) <= 10:
                            assert is_chordal_bipartite(len(nodes), {i for i, v in enumerate(base) if v < s}, copied)
                            stats['chordal_copy_graphs'] += 1
                        stats['zero_copy_structures'] += k == 0
    # A genuine chordal atom outside width two, and a width-two nonchordal atom.
    for rows in ((7, 7, 7), (3, 6, 5)):
        edges = edges_of(rows, 3, 1, ((0, 0, 0),) * 3)
        decomp = tree_bags(6, edges)
        assert (decomp is None) == (rows == (7, 7, 7))
        for seam in [(), (0,), (0, 3)]:
            nodes, base, copied = copy_graph(6, seam, edges, 2)
            if decomp:
                check_bags(len(nodes), copied, *copied_bags(nodes, seam, 2, *decomp))
                stats['copied_tree_decompositions'] += 1
            else:
                assert is_chordal_bipartite(len(nodes), {i for i, v in enumerate(base) if v < 3}, copied)
                stats['chordal_copy_graphs'] += 1


def counts_family(rows, n, m, stats):
    s, vertices = len(rows), len(rows) + n
    identity = tuple((0,) * n for _ in rows)
    oo = configurations(vertices, m, edges_of(rows, n, m, identity))
    profiles = list(product(range(m + 1), repeat=vertices))
    for gain in normalized_gains(rows, n, m):
        edges = edges_of(rows, n, m, gain)
        cc = configurations(vertices, m, edges)
        seams = [()] + [(v,) for v in range(vertices)] + [(x, y) for x, y, _ in edges]
        for seam in seams:
            boundary_edges = [(seam.index(x), seam.index(y), p) for x, y, p in edges
                              if x in seam and y in seam]
            boundaries = configurations(len(seam), m, boundary_edges)
            for k in range(3):
                nodes, base, copied = copy_graph(vertices, seam, edges, k)
                copied_counts = direct_counts(len(nodes), m, copied)
                for a in profiles:
                    aa = tuple(a[v] for v in seam)
                    pins = boundaries.get(aa, ())
                    fibres = Counter(tuple(config[v] for v in seam) for config in cc.get(a, ()))
                    ar = tuple(a[v] for v in base)
                    lhs = copied_counts[ar]
                    rhs = sum(fibres[pin] ** k for pin in pins)
                    assert lhs == rhs, (rows, n, m, gain, seam, k, a)
                    stats['copy_power_identities'] += 1
                    stats['zero_copy_identities'] += k == 0
                    if k != 1:
                        continue
                    p = len(oo.get(a, ()))
                    for pin in pins:
                        assert len(pins) * fibres[pin] <= p
                        stats['atom_boundary_fibre_bounds'] += 1
                        stats['zero_fibres'] += fibres[pin] == 0
                    if len(seam) == 1:
                        assert len(pins) == comb(m, a[seam[0]])
                    elif len(seam) == 2:
                        u, v = seam
                        factor = comb(m, a[u]) * comb(m - a[u], a[v]) if a[u] + a[v] <= m else 0
                        assert len(pins) == factor
                    stats['boundary_normalizations'] += 1


def controls():
    # A shared nonedge can combine two paths into an induced C6.
    edges = [(0, 1, (0, 1)), (1, 2, (0, 1)), (2, 3, (0, 1))]
    nodes, _, copied = copy_graph(4, (0, 3), edges, 2)
    adj = [set() for _ in nodes]
    for x, y, _ in copied:
        adj[x].add(y); adj[y].add(x)
    assert len(nodes) == 6 and all(len(ns) == 2 for ns in adj)
    # Dropping the seam at k=0 incorrectly replaces its legal configuration count by one.
    maps = permutation_maps(2)
    nodes, _, copied = copy_graph(2, (0, 1), [(0, 1, maps[1])], 0)
    assert len(configurations(len(nodes), 2, copied)[(1, 1)]) == 2
    return [
        {'status': 'REFUTED-STRENGTHENING', 'claim': 'Copying along any two vertices preserves chordal bipartiteness.',
         'fixture': 'Two copies of a length-three path share their nonadjacent endpoints, producing induced C6.'},
        {'status': 'REFUTED-STRENGTHENING', 'claim': 'Zero copies always have coefficient one.',
         'fixture': 'The induced actual edge remains; M=2 singleton ranks have two legal boundary configurations.'}]


def run():
    stats = Counter()
    structural(stats)
    for m in range(3):
        for s in range(3):
            for n in range(3):
                for rows in product(range(1 << n), repeat=s):
                    counts_family(rows, n, m, stats)
    for rows, n in [((), 0), ((0,), 1), ((1,), 1), ((3,), 2), ((3, 3), 2)]:
        counts_family(rows, n, 3, stats)
    return {'status': 'COMPUTATIONAL', 'result': 'PASS', 'counts': dict(stats),
            'scope': 'Copy bags for all bipartite bases with <=5 vertices, <=3 on either side, every empty/root/actual-edge seam and 0..3 copies; direct induced-cycle checks when copied size <=10, plus K3,3/C6 fixtures. Configuration powers for all 0..2-by-0..2 bases, M=0..2 and all gains modulo left gauges, 0..2 copies and all profiles; M=3 on five specified small bases.',
            'negative_controls': controls(), 'role': 'Finite diagnostics only; no Lean premise.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    data = json.dumps(run(), indent=2) + '\n'
    if args.output:
        args.output.write_text(data)
    print(data, end='')
