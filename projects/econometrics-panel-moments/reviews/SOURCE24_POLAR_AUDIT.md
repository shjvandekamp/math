# Independent audit of the auxiliary polar correction

15 October 2026. Internal read-only mathematical review by a separate Astra
explorer, with independent exact checks by the primary agent. This is not
external peer review or a Lean theorem audit.

**Result:** the all-even-length correction is mathematically consistent and
establishes a nonzero shared-new polar determinant with the explicit pole
and finite-parameter conditions below. Together with the odd-length leading
calculation, it supplies this polar half for every auxiliary length. It does
not establish the full equation-(24) determinant.

The review checked the derivation in
[the induction note](../research/SOURCE24_INDUCTION.md), including its
constant-real-span interpretation:

- The four Laurent shift reductions follow from the scalar parity identity,
  its explicitly allowed multiplication by the evaluation variable, and the
  two available defects. No quotient-ring multiplication is assumed.
- The map from the two-dimensional even kernel to its last-word coefficients
  is invertible, with determinant `cd(rho−1)/(c−d)^2`.
- Differentiating only the last transition, with row-one leakage suppressed,
  gives the claimed two kernel derivatives.
- The row-zero pole is removed with the **constant** coefficient
  `R_d(−1/(eta e))`. Its remaining affine term is retained.
- The resulting two affine remainders have coefficient determinant
  `rho/[eta(rho−1)^4] * [rho−eta+(c/e)(eta−1)]`.
  For `rho=2`, `eta=3`, and `c_t=5^(t−1)`, its bracket is
  `−1+2*5^(m−2)>0` for every even `m>=2`.
- The positive common matrix
  `G_M=[[1,1,1],[1,M,M/3],[1,3,2]]` realizes the odds ratios and leakage
  limit, with determinant `1+M/3`. After the explicit nonzero column and
  residue normalizations, finite large `M` and small positive earlier
  leakage parameters preserve nonvanishing.

Three qualifications are essential. First, the original scalar functions
vanish at zero and are bounded at infinity. The nullrelation cancels the
moving-pole double terms, leaving only simple permitted poles. Hence zero
finite residues implies a zero function, and function independence detects
the polar coordinates. Second, the boundary point does not itself satisfy
all two-dimensional pole geometry. Those separately established nonzero
polynomial conditions are imposed by perturbation inside the determinant's
open nonvanishing neighborhood. Third, the regular Schur half and the full
source-family determinant remain unproved. The scalar-covariate transport
lemma alone does not discharge either obligation.

The separate standard-library calculation
[binary_polar_derivative.py](../exploration/binary_polar_derivative.py)
solves constant Laurent kernels and checks the displayed reductions exactly
at eight rational parameter fixtures, with 48 actual product-derivative
comparisons. Results are saved in
[binary-polar-derivative-results.json](../exploration/binary-polar-derivative-results.json).
Those finite checks corroborate the derivation and do not substitute for
its all-length argument. No Lean process was run by the reviewer.
