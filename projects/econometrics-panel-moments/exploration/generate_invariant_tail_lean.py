#!/usr/bin/env python3
"""Emit untrusted Lean data and kernel checks from the saved finite certificate.

This does not rerun the Q(r) calculation. Read the three saved rational
matrices, clear denominators separately in each column, and compute right
inverse candidates modulo 1000003. Lean verifies all candidates in its kernel.
The actual-function-to-matrix bridge remains external to these modules.
"""

from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import resource
import signal
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'certificates/source24_invariant_tail_base.json'
DEST = ROOT / 'formal/PanelMoments'
PRIME = 1000003


def inverse_mod(matrix):
    n = len(matrix)
    work = [[entry % PRIME for entry in row] + [int(i == j) for j in range(n)]
            for i, row in enumerate(matrix)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if work[i][j])
        work[j], work[pivot] = work[pivot], work[j]
        unit = pow(work[j][j], -1, PRIME)
        work[j] = [entry * unit % PRIME for entry in work[j]]
        for i in range(n):
            if i != j:
                factor = work[i][j]
                work[i] = [(x - factor * y) % PRIME for x, y in zip(work[i], work[j])]
    result = [row[n:] for row in work]
    assert all(sum(matrix[i][s] * result[s][j] for s in range(n)) % PRIME == int(i == j)
               for i in range(n) for j in range(n))
    return result


def lean_number(value):
    value = Fraction(value)
    if value.denominator == 1:
        return str(value.numerator)
    return f'({value.numerator} / {value.denominator})'


def vector(values):
    return '![' + ', '.join(lean_number(value) for value in values) + ']'


def matrix(values):
    return '![' + ',\n   '.join(vector(row) for row in values) + ']'


def assemble_rows(name, statement, prefix, n):
    return (f'theorem {name} :\n    {statement} := by\n  funext i\n  fin_cases i\n' +
            ''.join(f'  · exact {prefix}_{i}\n' for i in range(n)) + '\n')


def generate():
    raw = SOURCE.read_bytes()
    source = json.loads(raw)
    assert source['all_prescribed_checks_passed']
    assert [stage['length'] for stage in source['stages']] == [3, 4, 5]
    source_hash = hashlib.sha256(raw).hexdigest()
    generator_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    data = ['''import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
set_option Elab.async false

/-!
# Displayed finite invariant-tail coefficient matrices

Generated from the saved JSON by exploration/generate_invariant_tail_lean.py.
These are untrusted literal data, not assumed mathematical results. The
companion certificate checks the integer column scalings and modular inverse
identities in Lean's kernel. It proves the displayed rational determinants
nonzero. Identification with the actual rational-function construction is
external; no source-family or all-length independence theorem is claimed.

Rows are ascending polynomial coefficients. Columns retain the saved order
S_k, 1, W0, W1, with new N columns preceding transported old columns in S_k.
''', f'\nInput JSON SHA-256: {source_hash}\nGenerator SHA-256: {generator_hash}\n',
            '-/\n\nnamespace PanelMoments.SourceInvariantTailBase\n\n']
    proof = ['''import PanelMoments.SourceInvariantTailBaseData
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-!
# Kernel-checked nonzero determinants of the displayed finite matrices

Every scalar data identity and inverse identity below is checked with
`decide +kernel`. The integer and rational determinant conclusions follow
from determinant functoriality and the checked column scalings. No external
determinant value is trusted. The bridge from actual Q(r) functions to the
displayed coefficient matrices remains external to this formalization.
-/

namespace PanelMoments.SourceInvariantTailBase

local instance : Fact (1 < 1000003) := ⟨by decide⟩

theorem integer_det_ne_zero_of_modular_inverse {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    (M B : Matrix (Fin n) (Fin n) (ZMod 1000003))
    (hmap : A.map (Int.castRingHom (ZMod 1000003)) = M)
    (hinv : M * B = 1) : A.det ≠ 0 := by
  have hm : M.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hinv
  intro hzero
  apply hm
  calc
    M.det = (A.map (Int.castRingHom (ZMod 1000003))).det :=
      congrArg Matrix.det hmap.symm
    _ = (Int.castRingHom (ZMod 1000003)) A.det :=
      ((Int.castRingHom (ZMod 1000003)).map_det A).symm
    _ = 0 := by rw [hzero, map_zero]

theorem rational_det_ne_zero_of_integer_column_scaling {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (scales : Fin n → ℤ) (hA : A.det ≠ 0)
    (hscale : A.map (Int.castRingHom ℚ) =
      Matrix.of (fun i j => (scales j : ℚ) * Q i j)) : Q.det ≠ 0 := by
  have hcast : (A.map (Int.castRingHom ℚ)).det ≠ 0 := by
    have hd : (A.det : ℚ) = (A.map (Int.castRingHom ℚ)).det :=
      (Int.castRingHom ℚ).map_det A
    rw [← hd]
    exact Int.cast_ne_zero.mpr hA
  intro hzero
  apply hcast
  rw [hscale, Matrix.det_mul_row, hzero, mul_zero]

''']
    for stage in source['stages']:
        k, n = stage['length'], stage['dimension']
        q = [[Fraction(value) for value in row] for row in stage['exact_rational_coefficient_matrix']]
        assert n == 3 * k + 1 and len(q) == n and all(len(row) == n for row in q)
        serialized = json.dumps(stage['exact_rational_coefficient_matrix'], separators=(',', ':')).encode()
        assert hashlib.sha256(serialized).hexdigest() == stage['coefficient_matrix_sha256']
        scales = [math.lcm(*(q[i][j].denominator for i in range(n))) for j in range(n)]
        integer = [[int(q[i][j] * scales[j]) for j in range(n)] for i in range(n)]
        assert all(Fraction(integer[i][j], scales[j]) == q[i][j] for i in range(n) for j in range(n))
        residue = [[entry % PRIME for entry in row] for row in integer]
        inverse = inverse_mod(residue)
        data.extend([
            f'/-- Length {k}; saved coefficient-matrix SHA-256: {stage["coefficient_matrix_sha256"]}. -/\n',
            f'def coefficientMatrix{k} : Matrix (Fin {n}) (Fin {n}) ℚ :=\n  {matrix(q)}\n\n',
            f'def columnScales{k} : Fin {n} → ℤ :=\n  {vector(scales)}\n\n',
            f'def integerMatrix{k} : Matrix (Fin {n}) (Fin {n}) ℤ :=\n  {matrix(integer)}\n\n',
            f'def residueMatrix{k} : Matrix (Fin {n}) (Fin {n}) (ZMod 1000003) :=\n  {matrix(residue)}\n\n',
            f'def inverseMatrix{k} : Matrix (Fin {n}) (Fin {n}) (ZMod 1000003) :=\n  {matrix(inverse)}\n\n'])
        for i in range(n):
            proof.extend([
                f'theorem stage{k}_mod_row_{i} :\n'
                f'    (integerMatrix{k}.map (Int.castRingHom (ZMod 1000003))) {i} = residueMatrix{k} {i} := by\n'
                '  funext j\n  fin_cases j <;> decide +kernel\n\n',
                f'theorem stage{k}_inverse_row_{i} :\n'
                f'    (residueMatrix{k} * inverseMatrix{k}) {i} =\n'
                f'      (1 : Matrix (Fin {n}) (Fin {n}) (ZMod 1000003)) {i} := by\n'
                '  funext j\n  fin_cases j <;> decide +kernel\n\n',
                f'theorem stage{k}_scaled_row_{i} :\n'
                f'    (integerMatrix{k}.map (Int.castRingHom ℚ)) {i} =\n'
                f'      (fun j => (columnScales{k} j : ℚ) * coefficientMatrix{k} {i} j) := by\n'
                '  funext j\n  fin_cases j <;> decide +kernel\n\n'])
        proof.extend([
            assemble_rows(f'integerMatrix{k}_mod',
                          f'integerMatrix{k}.map (Int.castRingHom (ZMod 1000003)) = residueMatrix{k}',
                          f'stage{k}_mod_row', n),
            assemble_rows(f'residueMatrix{k}_inverse', f'residueMatrix{k} * inverseMatrix{k} = 1',
                          f'stage{k}_inverse_row', n),
            assemble_rows(f'integerMatrix{k}_scaled',
                          f'integerMatrix{k}.map (Int.castRingHom ℚ) =\n'
                          f'      Matrix.of (fun i j => (columnScales{k} j : ℚ) * coefficientMatrix{k} i j)',
                          f'stage{k}_scaled_row', n),
            f'theorem integerMatrix{k}_det_ne_zero : integerMatrix{k}.det ≠ 0 :=\n'
            f'  integer_det_ne_zero_of_modular_inverse integerMatrix{k} residueMatrix{k} inverseMatrix{k}\n'
            f'    integerMatrix{k}_mod residueMatrix{k}_inverse\n\n',
            f'/-- The exact displayed length-{k} rational matrix has nonzero determinant.\n'
            'Its identification with the actual scalar functions is not formalized here. -/\n'
            f'theorem coefficientMatrix{k}_det_ne_zero : coefficientMatrix{k}.det ≠ 0 :=\n'
            f'  rational_det_ne_zero_of_integer_column_scaling coefficientMatrix{k} integerMatrix{k}\n'
            f'    columnScales{k} integerMatrix{k}_det_ne_zero integerMatrix{k}_scaled\n\n'])
    data.append('end PanelMoments.SourceInvariantTailBase\n')
    proof.append('end PanelMoments.SourceInvariantTailBase\n')
    data_path = DEST / 'SourceInvariantTailBaseData.lean'
    proof_path = DEST / 'SourceInvariantTailBaseCertificate.lean'
    data_path.write_text(''.join(data))
    proof_path.write_text(''.join(proof))
    return dict(input_sha256=source_hash, generator_sha256=generator_hash,
                dimensions=[10, 13, 16], definitions=15, theorems=134,
                files=[str(data_path), str(proof_path)])


def main():
    started = time.monotonic()

    def guard(_signal, _frame):
        if time.monotonic() - started >= 28:
            raise TimeoutError('Bounded data-generation time limit exceeded.')
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform != 'darwin':
            rss *= 1024
        if rss >= 95 * 1024 ** 2:
            raise MemoryError('Bounded data-generation memory limit exceeded.')

    signal.signal(signal.SIGALRM, guard)
    signal.setitimer(signal.ITIMER_REAL, .05, .05)
    result = generate()
    result['elapsed_seconds'] = time.monotonic() - started
    signal.setitimer(signal.ITIMER_REAL, 0)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
