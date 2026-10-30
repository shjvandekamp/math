#!/usr/bin/env python3
"""Bounded, standard-library numerical probe of the specified PECE recurrence.

This is discovery evidence, NOT a certificate. It never evaluates exp(G), so a
large Re(G) is recorded without creating an artificial floating-point overflow
in the final exponential. Nonfinite internal iterates are reported separately.
No convergence order is estimated or inferred.
"""
import argparse
import json
import math


def solve(alpha, maturity, steps, frequency, damping=-2.0,
          gamma=1.0, nu=1.0, theta=1.0, variance=1.0, rho=-0.5):
    dt = maturity / steps
    a = dt ** alpha / math.gamma(alpha + 2)
    b = dt ** alpha / math.gamma(alpha + 1)
    xi = complex(frequency, damping)
    c = (gamma * nu) ** 2 / 2

    def f(z):
        return -(xi * xi + 1j * xi) / 2 + gamma * (1j * xi * rho * nu - 1) * z + c * z * z

    h = [0j]
    fvals = [f(0j)]
    for n in range(steps):
        pred = sum(b * ((n + 1 - j) ** alpha - (n - j) ** alpha) * fvals[j]
                   for j in range(n + 1))
        weights = [a * (n ** (alpha + 1) - (n - alpha) * (n + 1) ** alpha)]
        weights += [a * ((n - j + 2) ** (alpha + 1) + (n - j) ** (alpha + 1)
                         - 2 * (n - j + 1) ** (alpha + 1)) for j in range(1, n + 1)]
        node = sum(w * z for w, z in zip(weights, fvals)) + a * f(pred)
        if not math.isfinite(abs(node)):
            return {"status": "nonfinite_internal_iterate", "first_node": n + 1}
        h.append(node)
        fvals.append(f(node))
    js = [theta * gamma * z + variance * fz for z, fz in zip(h, fvals)]
    exponent = dt * (js[0] / 2 + sum(js[1:-1]) + js[-1] / 2)
    if not math.isfinite(exponent.real):
        return {"status": "nonfinite_exponent"}
    return {"status": "finite", "exponent_real": exponent.real,
            "exponent_imag": exponent.imag, "max_node_modulus": max(map(abs, h))}


def leading_log(alpha, maturity, steps):
    """Predicted exact leading coefficient's logarithm, evaluated numerically."""
    dt = maturity / steps
    loga = alpha * math.log(dt) - math.lgamma(alpha + 2)
    logb = alpha * math.log(dt) - math.lgamma(alpha + 1)
    logc = math.log(0.5)
    logL = loga + logc + 2 * logb - math.log(4)
    for _ in range(1, steps):
        logL = loga + 2 * logb + 3 * logc + 4 * logL
    return math.log(dt / 2) + logc + 2 * logL


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="discovery/numerical_probe.json")
    args = parser.parse_args()
    rows = []
    for steps in (1, 2, 4, 8, 16, 32):
        for u in (0, 1, 2, 4, 8, 16, 32, 64):
            try:
                result = solve(0.75, 1.0, steps, u)
            except OverflowError:
                result = {"status": "floating_point_overflow"}
            rows.append({"steps": steps, "u": u, **result})
    output = {
        "proof_status": "illustration_only_not_a_certificate",
        "parameters": {"H": 0.25, "alpha": 0.75, "T": 1, "gamma": 1,
                       "nu": 1, "theta": 1, "V0": 1, "rho": -0.5, "R": -2,
                       "S0": 1, "K": 1, "r": 0},
        "rows": rows,
        "leading_terms": [{"steps": m, "degree_h": 4 ** m,
                           "degree_exponent": 2 * 4 ** m,
                           "log_leading_coefficient": leading_log(0.75, 1, m)}
                          for m in (1, 2, 4, 8)],
    }
    with open(args.output, "w") as out:
        json.dump(output, out, indent=2, allow_nan=False)
        out.write("\n")
    print(f"Wrote {len(rows)} illustrative samples to {args.output}; these are not proof.")


if __name__ == "__main__":
    main()
