#!/usr/bin/env python3
"""Exact actual-kernel cubic source minor; not the projected Schur minor.

Standard library only. The dual variable differentiates X=(x,1,1) at x=1.
The time curve is (u,v)=(1+t,1+t^2). No generic-rank conclusion is inferred.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import resource
import signal
import sys
import time


@dataclass(frozen=True)
class Jet:
    value: F
    derivative: F = F(0)

    @staticmethod
    def of(x):
        return x if isinstance(x, Jet) else Jet(F(x))

    def __add__(self, other):
        b = Jet.of(other)
        return Jet(self.value+b.value, self.derivative+b.derivative)

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.value, -self.derivative)

    def __sub__(self, other):
        return self + -Jet.of(other)

    def __rsub__(self, other):
        return Jet.of(other) + -self

    def __mul__(self, other):
        b = Jet.of(other)
        return Jet(self.value*b.value,
                   self.derivative*b.value+self.value*b.derivative)

    __rmul__ = __mul__

    def __truediv__(self, other):
        b = Jet.of(other)
        assert b.value
        return Jet(self.value/b.value,
                   (self.derivative*b.value-self.value*b.derivative)/b.value**2)


def add(a, b):
    return [[a[i][j]+b[i][j] for j in range(3)] for i in range(3)]


def neg(a):
    return [[-v for v in row] for row in a]


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    return [[sum((a[i][k]*b[k][j] for k in range(3)), Jet.of(0))
             for j in range(3)] for i in range(3)]


def diag(v):
    return [[Jet.of(v[i]) if i == j else Jet.of(0) for j in range(3)]
            for i in range(3)]


def comm(a, b):
    return sub(mul(a, b), mul(b, a))


def det(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def maximum_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == 'darwin' else 1024*value


def calculate():
    started = time.monotonic()
    x = [Jet(F(1),F(1)), Jet.of(1), Jet.of(1)]
    numerator = [[(1+int(i == j))*x[j] for j in range(3)] for i in range(3)]
    denominator = [sum(row, Jet.of(0)) for row in numerator]
    k = [[numerator[i][j]/denominator[i] for j in range(3)] for i in range(3)]
    d, e = diag([0,1,0]), diag([0,0,1])
    col1, col2 = diag([row[1] for row in k]), diag([row[2] for row in k])
    u = sub(mul(k,d), mul(col1,k))
    v = sub(sub(mul(k,e),mul(col2,k)),mul(col1,u))
    checks = []

    def check(name, left, right):
        assert left == right, (name,left,right)
        checks.append(name)

    # Independently expand each actual row numerator/normalizer through t^2.
    for i in range(3):
        den1, den2 = numerator[i][1], numerator[i][2]
        for j in range(3):
            num1 = numerator[i][j] if j == 1 else Jet.of(0)
            num2 = numerator[i][j] if j == 2 else Jet.of(0)
            direct_u = (num1-den1*k[i][j])/denominator[i]
            direct_v = (num2-den1*direct_u-den2*k[i][j])/denominator[i]
            check(f'actual first Taylor coefficient {i},{j}',u[i][j],direct_u)
            check(f'actual second Taylor coefficient {i},{j}',v[i][j],direct_v)
    s = add(add(mul(mul(comm(k,u),k),v),mul(comm(u,v),mul(k,k))),
            mul(mul(comm(v,k),k),u))
    y = mul(diag(x),s)
    values = [[z.value for z in row] for row in y]
    derivatives = [[z.derivative for z in row] for row in y]
    expected_values = [[6,-13,7],[7,-12,5],[5,-11,6]]
    expected_derivatives = [[120,-261,141],[29,-64,35],[23,-63,40]]
    for i in range(3):
        for j in range(3):
            check(f'cubic row value {i},{j}',values[i][j],F(expected_values[i][j],4096))
            check(f'cubic row derivative {i},{j}',derivatives[i][j],F(expected_derivatives[i][j],65536))
        check(f'cubic row sum {i}',sum(values[i]),F(0))
        check(f'cubic derivative row sum {i}',sum(derivatives[i]),F(0))
    observation = [[values[j][1] for j in range(3)],
                   [values[j][2] for j in range(3)],
                   [derivatives[j][1] for j in range(3)]]
    minor = det(observation)
    check('ordinary cubic observation determinant',minor,F(397,2**37))
    check('source cubic determinant coefficient at q=3',(-2)**3*minor,-F(397,2**34))
    new_empty = mul(diag(x),sub(diag([1,1,1]),k))
    empty_observation = [[new_empty[j][1].value for j in range(3)],
                         [new_empty[j][2].value for j in range(3)],
                         [new_empty[j][1].derivative for j in range(3)]]
    expected_empty = [[F(-1,4),F(1,2),F(-1,4)],
                      [F(-1,4),F(-1,4),F(1,2)],
                      [F(-1,8),F(1,8),F(1,16)]]
    for i in range(3):
        for j in range(3):
            check(f'actual new empty-source observation {i},{j}',
                  empty_observation[i][j],expected_empty[i][j])
    check('new empty-source observation determinant',det(empty_observation),F(3,256))
    return dict(status='passed', scope='ordinary actual-source cubic minor, not paired-eliminated',
                curve=dict(u='1+t',v='1+t^2',G='I+11^T',X='(x,1,1)'),
                exact_checks=len(checks), checks=checks,
                Y=[[str(z) for z in row] for row in values],
                Y_derivative=[[str(z) for z in row] for row in derivatives],
                observation_matrix=[[str(z) for z in row] for row in observation],
                observation_determinant=str(minor),
                source_coefficient_q3=str(-8*minor),
                new_empty_source_observation_matrix=[[str(z) for z in row] for row in empty_observation],
                new_empty_source_observation_determinant=str(det(empty_observation)),
                quotient_observation_obstruction='These observations are already onto on actual new empty sources; no nonzero linear combination annihilates that subspace.',
                all_length_tail_factor='4^(-3*(q-3)); justified separately by zero-sum row action',
                elapsed_seconds=time.monotonic()-started,
                max_rss_bytes=maximum_rss_bytes(),
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    started = time.monotonic()
    def guard(_signum, _frame):
        if time.monotonic()-started >= 28:
            raise TimeoutError('Single-run 28-second budget exhausted.')
        if maximum_rss_bytes() >= 95*1024**2:
            raise MemoryError('Single-run 95 MiB budget exhausted.')
    signal.signal(signal.SIGALRM,guard)
    signal.setitimer(signal.ITIMER_REAL,.05,.05)
    record = calculate()
    args.output.write_text(json.dumps(record,indent=2)+'\n')
    signal.setitimer(signal.ITIMER_REAL,0)
    print(json.dumps({k:record[k] for k in ('status','exact_checks','observation_determinant',
        'elapsed_seconds','max_rss_bytes')},sort_keys=True))
