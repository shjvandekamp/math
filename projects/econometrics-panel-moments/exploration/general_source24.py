#!/usr/bin/env python3
"""Exact external exploration of DHW equation (24), not a Lean proof.

Standard library only. Times, outcomes, and initial states are zero based.
The additional restriction in section 3.4 / footnote 8 is essential for T >= 5.
For Q = 3, j >= 2 requires the first j - 1 shared times to be 0,...,j-2.

We use the same scalar-covariate economic witness as exact_q3t4.py:
  pi[t][q][r] = 2 ** (q * (3 * (t + 1) + r)).
The integer row matrix K is M diag(A_y), where M is the actual source
moment matrix and A_y is the strictly positive ordinary path numerator.
Thus column clearing preserves real row rank. A nonzero minor modulo an
odd prime gives an exact integer nonzero minor, but the computation here
has not itself been verified by Lean.

Rows containing shared time zero split into three disjoint path blocks.
We eliminate those rows first and then reduce the extension rows in the
quotient. This supplies the full rank and a compact original-matrix minor
without retaining large matrices in the JSON result.

Reproduce the stored experiments from the project directory, in order:
  python3 exploration/general_source24.py --output exploration/general-source24-results.json
  python3 exploration/general_source24.py --periods 5 --transition22 17 --output exploration/general-source24-results.json --append
  python3 exploration/general_source24.py --periods 6 --primes 1000003 --transition22 17 --output exploration/general-source24-results.json --append

The perturbation sets gamma[2,2] = log(17) instead of log(16), leaving
the normalized transition table, scalar slopes, and covariates unchanged
in all other coordinates. Modular rank deficiencies do not by themselves
give real-rank upper bounds; only the displayed nonzero minors supply
integer and real rank lower bounds.
"""

import argparse
import hashlib
import importlib.util
import itertools as it
import json
import math
from pathlib import Path


Q = 3
DEFAULT_PRIMES = (1000003, 1000033)
DEFAULT_G = ((1, 1, 1), (1, 2, 4), (1, 4, 16))


def dimension(T):
    return Q**T - math.comb(3 * T, 2) + 6 * (T - 1)


def source_indices(T):
    """The constrained family (24), including its footnotes 7 and 8."""
    if T < 3:
        return []
    ans = []
    for j in range(T - 2):
        fixed = max(0, j - (Q - 2))
        for shared in it.combinations(range(T - 1), j):
            if shared[:fixed] != tuple(range(fixed)):
                continue
            remaining = sorted(set(range(T - 1)) - set(shared))
            s1 = remaining[0]
            for s2 in remaining[1:]:
                tail = sorted(set(remaining) - {s1, s2})
                tau1 = list(shared) + [s1] + tail + [s2, T - 1]
                tau2 = list(shared) + [s2] + tail + [s1, T - 1]
                for values in it.product(range(Q), repeat=j + 1):
                    ans.append(dict(j=j, shared=shared, s1=s1, s2=s2,
                                    values=values, tau1=tau1, tau2=tau2))
    return ans


def transformed_numerator(y, tau, initial, G):
    """The transformed numerator, with an arbitrary positive integer G."""
    T = len(y)
    sigma = dict(zip([T - 1] + tau[:-1], tau))
    exponent = (3 * y[sigma[T - 1]]
                + sum(3 * (t + 1) * y[sigma[t - 1]]
                      for t in range(1, T)))
    transitions = G[y[sigma[T - 1]]][initial]
    for t in range(1, T):
        transitions *= G[y[sigma[t - 1]]][y[t - 1]]
    return transitions << exponent


def source_row(paths, idx, initial=0, G=DEFAULT_G):
    row = []
    q = idx['values'][0]
    for y in paths:
        if any(y[t] != v for t, v in zip(idx['shared'], idx['values'][1:])):
            row.append(0)
            continue
        first = (transformed_numerator(y, idx['tau1'], initial, G)
                 if y[idx['s1']] == q else 0)
        second = (transformed_numerator(y, idx['tau2'], initial, G)
                  if y[idx['s2']] == q else 0)
        row.append(first - second)
    return row


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


class Echelon:
    """Exact modular row elimination, recording an original-row minor."""

    def __init__(self, ncols, prime):
        self.ncols = ncols
        self.prime = prime
        self.basis = {}
        self.rows = []
        self.columns = []
        self.determinant = 1

    def reduce(self, row):
        p = self.prime
        row = [x % p for x in row]
        for c in sorted(self.basis):
            factor = row[c]
            if factor:
                basis_row = self.basis[c]
                row[c:] = [(x - factor * y) % p
                           for x, y in zip(row[c:], basis_row[c:])]
        return row

    def add(self, row, row_id):
        row = self.reduce(row)
        c = next((c for c, x in enumerate(row) if x), None)
        if c is None:
            return False
        pivot = row[c]
        p = self.prime
        inverse = pow(pivot, -1, p)
        self.basis[c] = [x * inverse % p for x in row]
        self.rows.append(row_id)
        self.columns.append(c)
        self.determinant = self.determinant * pivot % p
        return True

    @property
    def rank(self):
        return len(self.basis)


def matrix_hash(rows):
    """SHA256 of decimal entries, commas between columns, LF after rows."""
    h = hashlib.sha256()
    for row in rows:
        h.update((','.join(map(str, row)) + '\n').encode())
    return h.hexdigest()


def group_key(idx):
    return idx['j'], idx['shared'], idx['s2']


def verify_initial_rescalings(paths, indices, rows, G):
    # The indicators fix the first generated outcome in both permutations.
    # Therefore changing the initial state multiplies each entire row by
    # G[first_generated_outcome][initial], including entries equal to zero.
    assert all(G[q][0] == 1 for q in range(Q))
    for initial in (1, 2):
        for idx, row in zip(indices, rows):
            first_outcome = idx['values'][1 if idx['j'] else 0]
            multiplier = G[first_outcome][initial]
            assert source_row(paths, idx, initial, G) == [multiplier * x for x in row]
    return dict(checked_initial_states=[0, 1, 2],
                method='exact integer comparison of every matrix entry',
                row_multiplier='G[values[1]][initial] if j>0; G[values[0]][initial] if j=0; G[q][0]=1.',
                consequence='All three initial states have the same real rank, and the same modular rank at primes not dividing any entry of G.')


def verify_t4_consistency(indices, rows):
    location = Path(__file__).with_name('exact_q3t4.py')
    spec = importlib.util.spec_from_file_location('previous_q3t4', location)
    old = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(old)
    assert indices == old.source_indices()
    assert rows == old.moment_numerators(old.PI, initial=0)
    return 'Exact equality of all row indices and all integer entries with unchanged exact_q3t4.py.'


def check_prime(T, indices, rows, prime):
    block_width = Q ** (T - 1)
    lifted_ids = [i for i, idx in enumerate(indices) if 0 in idx['shared']]
    extension_ids = [i for i, idx in enumerate(indices) if 0 not in idx['shared']]
    assert all(indices[i]['j'] <= 1 for i in extension_ids)
    blocks = []
    lifted_reports = []
    full_minor_rows = []
    full_minor_columns = []
    full_minor_det = 1
    for first_outcome in range(Q):
        ids = [i for i in lifted_ids if indices[i]['values'][1] == first_outcome]
        start = first_outcome * block_width
        stop = start + block_width
        e = Echelon(block_width, prime)
        for i in ids:
            assert not any(rows[i][:start]) and not any(rows[i][stop:])
            e.add(rows[i][start:stop], i)
        free = [c for c in range(block_width) if c not in e.basis]
        blocks.append((e, free))
        lifted_reports.append(dict(first_outcome=first_outcome, row_count=len(ids),
                                   rank=e.rank, quotient_columns=len(free)))
        full_minor_rows.extend(e.rows)
        full_minor_columns.extend(start + c for c in e.columns)
        full_minor_det = full_minor_det * e.determinant % prime

    quotient_columns = [a * block_width + c
                        for a, (_, free) in enumerate(blocks) for c in free]
    quotient_rows = []
    for i in extension_ids:
        reduced = []
        for a, (e, free) in enumerate(blocks):
            block = e.reduce(rows[i][a * block_width:(a + 1) * block_width])
            reduced.extend(block[c] for c in free)
        quotient_rows.append(reduced)

    extension_echelon = Echelon(len(quotient_columns), prime)
    group_reports = []
    for key, group in it.groupby(zip(extension_ids, quotient_rows),
                                 key=lambda pair: group_key(indices[pair[0]])):
        group = list(group)
        before = extension_echelon.rank
        supports = [set() for _ in range(Q)]
        offsets = [0]
        for _, free in blocks:
            offsets.append(offsets[-1] + len(free))
        for i, row in group:
            extension_echelon.add(row, i)
            for a in range(Q):
                supports[a].update(c for c in range(offsets[a], offsets[a + 1])
                                   if row[c])
        j, shared, s2 = key
        group_reports.append(dict(j=j, shared=list(shared), s2=s2,
                                  row_count=len(group),
                                  added_rank=extension_echelon.rank - before,
                                  cumulative_extension_rank=extension_echelon.rank,
                                  supported_quotient_columns_by_first_outcome=[len(s) for s in supports]))

    lifted_rank = sum(e.rank for e, _ in blocks)
    rank = lifted_rank + extension_echelon.rank
    full_minor_rows.extend(extension_echelon.rows)
    full_minor_columns.extend(quotient_columns[c] for c in extension_echelon.columns)
    full_minor_det = full_minor_det * extension_echelon.determinant % prime
    # Reordering rows and columns as recorded gives this determinant: the
    # lifted block elimination followed by quotient elimination is triangular.
    assert len(full_minor_rows) == len(full_minor_columns) == rank
    assert full_minor_det != 0
    return dict(prime=prime, ranks_by_initial_state={str(a): rank for a in range(Q)},
                initial_state_method='One elimination for initial zero; exact entrywise row rescaling verified for initial one and two.',
                lifted_row_count=len(lifted_ids), lifted_rank=lifted_rank,
                expected_lifted_rank=3 * dimension(T - 1), lifted_blocks=lifted_reports,
                extension_row_count=len(extension_ids),
                extension_quotient_shape=[len(extension_ids), len(quotient_columns)],
                extension_quotient_rank=extension_echelon.rank,
                expected_extension_rank=3 * (T - 2) * (3 * T - 8),
                extension_quotient_sha256=matrix_hash(quotient_rows),
                extension_groups=group_reports,
                nonzero_original_integer_minor_mod_prime=dict(
                    size=rank, rows=full_minor_rows, columns=full_minor_columns,
                    determinant_mod_prime=full_minor_det,
                    row_and_column_order='Use the listed order, not sorted order.'),
                full_row_rank=(rank == len(rows)))


def run_period(T, primes, G):
    indices = source_indices(T)
    paths = list(it.product(range(Q), repeat=T))
    assert len(indices) == dimension(T)
    assert len({(idx['j'], idx['shared'], idx['s2'], idx['values']) for idx in indices}) == len(indices)
    rows = [source_row(paths, idx, G=G) for idx in indices]
    rescalings = verify_initial_rescalings(paths, indices, rows, G)
    groups = []
    for (j, shared), group in it.groupby(indices, key=lambda idx: (idx['j'], idx['shared'])):
        groups.append(dict(j=j, shared=list(shared), row_count=sum(1 for _ in group)))
    result = dict(T=T, path_count=len(paths), moment_count=len(indices),
                  structural_moment_dimension=dimension(T),
                  counts_by_j={str(j): sum(idx['j'] == j for idx in indices)
                               for j in range(T - 2)},
                  groups_by_shared_times=groups,
                  matrix_integer_sha256=matrix_hash(rows),
                  initial_rescaling=rescalings)
    if T == 4 and G == DEFAULT_G:
        result['existing_t4_consistency'] = verify_t4_consistency(indices, rows)
    result['modular_checks'] = []
    for prime in primes:
        assert all(x % prime for row in G for x in row)
        check = check_prime(T, indices, rows, prime)
        result['modular_checks'].append(check)
        print(json.dumps(dict(T=T, prime=prime, count=len(indices),
                              ranks=check['ranks_by_initial_state'],
                              lifted_rank=check['lifted_rank'],
                              extension_shape=check['extension_quotient_shape'],
                              extension_rank=check['extension_quotient_rank'])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--periods', nargs='+', type=int, default=[4, 5, 6])
    parser.add_argument('--primes', nargs='+', type=int, default=list(DEFAULT_PRIMES))
    parser.add_argument('--transition22', type=int, default=16,
                        help='G[2][2]; 16 is the original conic witness, 17 the first perturbation.')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--append', action='store_true',
                        help='Append this experiment to additional_experiments in an existing JSON output.')
    args = parser.parse_args()
    if any(T < 4 or T > 6 for T in args.periods):
        parser.error('This bounded exploration supports T = 4, 5, 6 only.')
    if any(p == 2 or not is_prime(p) for p in args.primes):
        parser.error('Every modulus must be an odd prime.')
    if args.transition22 <= 0:
        parser.error('transition22 must be positive.')
    if args.append and (args.output is None or not args.output.is_file()):
        parser.error('--append requires an existing --output file.')
    G = (DEFAULT_G[0], DEFAULT_G[1], (1, 4, args.transition22))
    result = dict(status='Exact external discovery; not Lean-verified and not an arbitrary-T proof.',
                  source='DHW arXiv:2610.17104v1, equation (24), section 3.4, footnotes 7 and 8.',
                  indexing='Zero based; lexicographic paths; source rows ordered by j, shared, s2, values.',
                  witness=dict(Q=Q, G=G, table='pi[t][q][r] = G[q][r] * 2^(3*q*(t+1))',
                               gamma='gamma[q,r] = log(G[q][r])', beta=[0, 1, 2],
                               covariates='x[t] = 3*(t+1)*log(2)'),
                  row_interpretation='K = M diag(A_y), where A_y is the positive ordinary path numerator. No row scaling is used to define K.',
                  shared_restriction='shared[:max(0,j-1)] == tuple(range(max(0,j-1)))',
                  induction_partition='Lifted: shared contains 0. Extension: j=0, or j=1 with shared[0]>0.',
                  certificate_interpretation='Listed minors are minors of integer K for initial state zero. Their nonzero determinant modulo an odd prime proves the corresponding integer determinant nonzero, contingent on this external program.',
                  periods=[run_period(T, args.primes, G) for T in args.periods])
    if args.output:
        if args.append:
            previous = json.loads(args.output.read_text())
            previous.setdefault('additional_experiments', []).append(result)
            result = previous
        args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
