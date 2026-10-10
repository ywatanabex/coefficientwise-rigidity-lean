#!/usr/bin/env python3
"""COMPUTATIONAL diagnostics for publication-boundary definitions and witnesses."""
import argparse
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path


def count(m, ranks, twist):
    choices = [list(map(frozenset, combinations(range(m), r))) if 0 <= r <= m else []
               for r in ranks]
    edges = [(0, 1), (1, 2), (2, 3), (3, 0)]
    return sum(all(not ({(twist[i] if (u, v) == (3, 0) else i) for i in sets[u]} & sets[v])
                       for u, v in edges) for sets in product(*choices))


def run():
    fixtures = []
    for m, twist, expected in [(2, (1, 0), (2, 0, 1)), (3, (1, 2, 0), (18, 15, 1))]:
        p = count(m, (1,) * 4, tuple(range(m)))
        z = count(m, (1,) * 4, twist)
        r = count(m - 2, (0,) * 4, tuple(range(m - 2)))
        assert (p, z, r) == expected and p - z == m * r
        fixtures.append({'M': m, 'ordinary': p, 'gained': z, 'reserve': r, 'deficit': p - z})
    # Direct coefficient convention for one isolated vertex: p=(1+x), p^0=1.
    reduced_polynomial = Counter(mask.bit_count() for mask in range(1 << (2 - 2)))
    shifted_polynomial = Counter({degree + 1: value for degree, value in reduced_polynomial.items()})
    internal_reserve = len(list(combinations(range(2 - 2), max(0 - 1, 0))))
    shifted_polynomial_coefficient = shifted_polynomial[0]
    paper_reserve = reduced_polynomial[-1]
    assert internal_reserve == 1 and paper_reserve == shifted_polynomial_coefficient == 0
    return {'status': 'COMPUTATIONAL', 'result': 'PASS', 'sharpness_fixtures': fixtures,
            'zero_rank_reserve': {'internal': internal_reserve, 'paper': paper_reserve,
                                 'shifted_coefficient': shifted_polynomial_coefficient},
            'scope': 'Only the two explicit C4 singleton profiles and the isolated-vertex boundary.',
            'role': 'Independent interpretation checks; kernel proofs are in Sharpness and PaperReserve.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(run(), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
