#!/usr/bin/env python3
"""COMPUTATIONAL diagnostics for finite construction trees, independent of Lean.

Counts literal selected-set assignments. Every leaf occurrence is separately
used as the designated quantitative witness; no finite test is a proof premise.
"""
import argparse
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
import json
from math import comb
from pathlib import Path
import random
from check_cone_elimination import permutation_maps
from check_star_contraction import flat
from check_replicas import tree_bags, check_bags, is_chordal_bipartite


@dataclass(frozen=True)
class Node:
    vertices: tuple
    edges: tuple
    children: tuple = ()


def atom(vertices, edges):
    return Node(tuple(sorted(vertices)), tuple(sorted(tuple(sorted(e)) for e in edges)))


def glue(left, right):
    seam = set(left.vertices) & set(right.vertices)
    assert len(seam) <= 2
    if len(seam) == 2:
        edge = tuple(sorted(seam))
        assert edge in left.edges and edge in right.edges
    return Node(tuple(sorted(set(left.vertices) | set(right.vertices))),
                tuple(sorted(set(left.edges) | set(right.edges))), (left, right))


def nodes(tree):
    yield tree
    for child in tree.children:
        yield from nodes(child)


def leaves(tree):
    if not tree.children:
        yield tree
    for child in tree.children:
        yield from leaves(child)


def bipartition(tree):
    adjacency = {v: set() for v in tree.vertices}
    for u, v in tree.edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    side = {}
    for v in tree.vertices:
        if v in side:
            continue
        side[v] = False
        pending = [v]
        while pending:
            u = pending.pop()
            for w in adjacency[u]:
                if w in side:
                    assert side[w] != side[u]
                else:
                    side[w] = not side[u]
                    pending.append(w)
    return side


def validate_atoms(tree):
    for leaf in leaves(tree):
        side = bipartition(leaf)
        index = {v: i for i, v in enumerate(leaf.vertices)}
        edges = [(index[u], index[v], None) for u, v in leaf.edges]
        bags = tree_bags(len(index), edges)
        if bags is not None:
            check_bags(len(index), edges, *bags)
        else:
            directed = [(u, v, None) if side[leaf.vertices[u]] else (v, u, None)
                        for u, v, _ in edges]
            assert is_chordal_bipartite(len(index), {index[v] for v in side if side[v]}, directed)


@lru_cache(maxsize=8192)
def configs(vertices, m, edges, a):
    """Exhaust all selected sets of the requested sizes; prune only actual conflicts."""
    choices = {v: tuple(s for s in range(1 << m) if s.bit_count() == r)
               for v, r in zip(vertices, a)}
    if any(not choices[v] for v in vertices):
        return ()
    degree = Counter(v for u, w, _ in edges for v in (u, w))
    order = sorted(vertices, key=lambda v: (len(choices[v]), -degree[v], v))
    selected = {}
    result = []

    def visit(k):
        if k == len(order):
            result.append(tuple(selected[v] for v in vertices))
            return
        v = order[k]
        for mask in choices[v]:
            selected[v] = mask
            if all(not (p[selected[x]] & selected[y]) for x, y, p in edges
                   if x in selected and y in selected):
                visit(k + 1)
        selected.pop(v, None)

    visit(0)
    return tuple(result)


def fixtures():
    c1 = atom(range(4), [(0, 1), (1, 2), (2, 3), (0, 3)])
    c2 = atom([0, 1, 4, 5], [(0, 1), (1, 4), (4, 5), (0, 5)])
    c3 = atom([4, 5, 6, 7], [(4, 5), (5, 6), (6, 7), (4, 7)])
    cv = atom([3, 4, 5, 6], [(3, 4), (4, 5), (5, 6), (3, 6)])
    complete = atom(range(6), [(u, v) for u in range(3) for v in range(3, 6)])
    long_cycle = atom([0, 3, 6, 7, 8, 9], [(0, 3), (3, 6), (6, 7), (7, 8), (8, 9), (0, 9)])
    edge = atom([0, 1], [(0, 1)])
    return [
        ('empty-with-empty', glue(atom([], []), atom([], []))),
        ('overlapping-singletons', glue(atom([0], []), atom([0], []))),
        ('repeated-edge', glue(edge, glue(edge, atom([0], [])))),
        ('three-edge-squares', glue(c1, glue(c2, c3))),
        ('vertex-squares-isolate', glue(glue(c1, cv), atom([7], []))),
        ('mixed-K33-C6-isolate', glue(atom([10], []), glue(complete, long_cycle))),
    ]


def profiles(tree, m, rng):
    n = len(tree.vertices)
    if m <= 1 or (m == 2 and n <= 8):
        return product(range(m + 1), repeat=n)
    side = bipartition(tree)
    chosen = {tuple(0 for _ in range(n)), tuple(m for _ in range(n)), tuple(1 for _ in range(n))}
    for v in tree.vertices:
        chosen.add(tuple(0 if w == v else 1 for w in tree.vertices))
        chosen.add(tuple(m if w == v else 0 for w in tree.vertices))
        if not any(v in e for e in tree.edges):
            chosen.add(tuple(m if w == v else 1 for w in tree.vertices))
    for a in product(range(1, m + 1), repeat=n):
        aa = dict(zip(tree.vertices, a))
        if all(aa[u] + aa[v] <= m for u, v in tree.edges):
            chosen.add(a)
    chosen.update(tuple(rng.randrange(m + 1) for _ in range(n)) for _ in range(64))
    chosen.add(tuple(1 if side[v] else m - 1 for v in tree.vertices))
    chosen.add(tuple(m - 1 if side[v] else 1 for v in tree.vertices))
    return sorted(chosen)


def check_tree(name, tree, m, stats, rng):
    validate_atoms(tree)
    all_nodes, all_leaves = list(nodes(tree)), list(leaves(tree))
    identity = permutation_maps(m)[0]
    maps = permutation_maps(m)
    cases = [tuple(identity for _ in tree.edges)]
    if m >= 2:
        for e in range(min(3, len(tree.edges))):
            cases.append(tuple(maps[1] if i == e else identity for i in range(len(tree.edges))))
        cases += [tuple(rng.choice(maps) for _ in tree.edges) for _ in range(2)]
    aa = tuple(profiles(tree, m, rng))
    for case in cases:
        gains = dict(zip(tree.edges, case))
        full_edges = tuple((u, v, gains[u, v]) for u, v in tree.edges)
        for a in aa:
            ranks = dict(zip(tree.vertices, a))
            records = {}
            for node in all_nodes:
                local = tuple(ranks[v] for v in node.vertices)
                edges = tuple((u, v, gains[u, v]) for u, v in node.edges)
                ordinary_edges = tuple((u, v, identity) for u, v in node.edges)
                z = configs(node.vertices, m, edges, local)
                p = configs(node.vertices, m, ordinary_edges, local)
                records[node] = (z, p)
                assert len(z) <= len(p), (name, m, a, node)
                stats['piece_comparisons'] += 1
                if m >= 2 and all(a):
                    reduced = tuple(ranks[v] - 1 for v in node.vertices)
                    rid = permutation_maps(m - 2)[0]
                    r = configs(node.vertices, m - 2,
                                tuple((u, v, rid) for u, v in node.edges), reduced)
                    records[node] += (r,)
            z, p = records[tree][:2]
            feasible = all(0 <= ranks[v] <= m for v in tree.vertices) and all(
                ranks[u] + ranks[v] <= m for u, v in tree.edges)
            assert bool(p) == feasible
            if feasible:
                active = [(u, v, gain) for u, v, gain in full_edges if ranks[u] and ranks[v]]
                assert (len(z) == len(p)) == flat(max(tree.vertices, default=-1) + 1, m, active)
                stats['active_flat_equality_cases'] += 1
                for piece in all_nodes:
                    zj, pj = records[piece][:2]
                    assert pj
                    assert (len(p) - len(z)) * len(pj) >= (len(pj) - len(zj)) * len(p)
                    stats['relative_piece_bounds'] += 1
            else:
                stats['infeasible_profiles'] += 1
            positions = {v: i for i, v in enumerate(tree.vertices)}
            for v in tree.vertices:
                counts = Counter(s[positions[v]] for s in z)
                multiplier = comb(m, ranks[v])
                assert all(multiplier * c <= len(p) for c in counts.values())
                stats['root_fibre_bounds'] += len(counts)
                stats['zero_root_fibres'] += multiplier - len(counts)
            for u, v in tree.edges:
                counts = Counter((s[positions[u]], s[positions[v]]) for s in z)
                multiplier = comb(m, ranks[u]) * comb(m - ranks[u], ranks[v])
                assert all(multiplier * c <= len(p) for c in counts.values())
                stats['edge_fibre_bounds'] += len(counts)
                stats['zero_edge_fibres'] += multiplier - len(counts)
            for node in all_nodes:
                if not node.children:
                    continue
                left, right = node.children
                seam = sorted(set(left.vertices) & set(right.vertices))
                getpin = lambda child, s: tuple(s[child.vertices.index(v)] for v in seam)
                for column in (0, 1):
                    ll = Counter(getpin(left, s) for s in records[left][column])
                    rr = Counter(getpin(right, s) for s in records[right][column])
                    assert len(records[node][column]) == sum(c * rr[pin] for pin, c in ll.items())
                    stats['exact_gluing_identities'] += 1
                zn, pn = records[node][:2]
                if pn:
                    zl, pl = records[left][:2]
                    zr, pr = records[right][:2]
                    assert (len(pn) - len(zn)) * len(pl) >= (len(pl) - len(zl)) * len(pn)
                    assert (len(pn) - len(zn)) * len(pr) >= (len(pr) - len(zr)) * len(pn)
                    stats['relative_seam_bounds'] += 2
                    if not seam:
                        assert len(zn) == len(zl) * len(zr)
                        assert len(pn) == len(pl) * len(pr)
                        stats['empty_seam_survival_products'] += 1
            if m >= 2 and all(a):
                reserve = len(records[tree][2])
                deficit = len(p) - len(z)
                for witness in all_leaves:
                    zw, pw, rw = records[witness]
                    if rw:
                        assert deficit * len(rw) >= (len(pw) - len(zw)) * reserve
                        stats['designated_witness_bounds'] += 1
                        stats['strict_witness_bounds'] += len(pw) > len(zw)
                    else:
                        assert reserve == 0
                        stats['zero_witness_reserve'] += 1
                stats['zero_union_reserve'] += reserve == 0
            stats['root_profiles'] += 1
        stats['cover_fixtures'] += 1


def control():
    m = 3
    maps = permutation_maps(m)
    swap = next(p for p in maps if p[1] == 2 and p[2] == 1 and p[4] == 4)
    tree = fixtures()[3][1].children[0]
    edges = tuple((u, v, swap if (u, v) == (0, 1) else maps[0]) for u, v in tree.edges)
    ordinary = tuple((u, v, maps[0]) for u, v in tree.edges)
    z, p = configs(tree.vertices, m, edges, (1,) * 4), configs(tree.vertices, m, ordinary, (1,) * 4)
    assert len(z) < len(p) and not flat(4, m, edges)
    zpin, ppin = sum(s[0] == 4 for s in z), sum(s[0] == 4 for s in p)
    assert zpin == ppin > 0
    return {'status': 'REFUTED-STRENGTHENING',
            'claim': 'Nonflatness forces strict inequality at every legal root pin.',
            'fixture': 'C4, M=3, singleton ranks, one transposition fixing colour 3; root fixed to colour 3.',
            'gained': len(z), 'ordinary': len(p), 'gained_root': zpin, 'ordinary_root': ppin}


def run():
    stats = Counter()
    rng = random.Random(20261010)
    for name, tree in fixtures():
        for m in range(4):
            check_tree(name, tree, m, stats, rng)
    assert stats['strict_witness_bounds'] and stats['zero_witness_reserve']
    return {'status': 'COMPUTATIONAL', 'result': 'PASS', 'seed': 20261010, 'counts': dict(stats),
            'scope': 'Six explicit construction trees, including three squares, mixed K3,3/C6, isolated vertices, repeated edge and empty pieces. M=0..3. All profiles at M<=1 and for <=8 vertices at M=2; every positive feasible profile plus specified boundary profiles and 64 seeded profiles otherwise. Identity, up to three single twists, two seeded gains at M>=2. Every atom and intermediate occurrence is checked for relative-deficit monotonicity; each leaf is a quantitative witness. Counts are test executions, not distinct isomorphism classes.',
            'negative_controls': [control()], 'role': 'Independent finite diagnostics; no Lean premise.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(run(), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
