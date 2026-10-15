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

## Follow-up: regular quotient coordinates

A subsequent read-only review checked the note's equations (S3)–(S7).
The no-new-pole space decomposes as the untransformed old space, the regular
canonical columns C, and the three polynomial rows H. The coordinate-edge
functionals annihilate the old and polynomial parts and give, for each old
line, an invertible diagonal scaling of the transpose of the new table's
inverse. The matching component's divided residue exists by the old
base-point vanishing condition. The proof must require every coordinate-edge
point to avoid every other old and new denominator line.

The transformed old single-block moments have a nonzero C correction; the
raw edge functionals do not annihilate them. The corrected Delta coordinates
do. After old-old double residues and new polar residues have been eliminated,
the divided old-line residue is a homogeneous linear zero-sum row. Its unique
decomposition into the three H rows and the old residue row defines Delta.
These coordinates are the identity on C and zero on transformed old
single-block and polynomial rows. The review checked this uniqueness and the
correction sign explicitly.

This gives complete coordinates for the remaining regular quotient. It does
not prove independence of the specified source columns in those coordinates
or nonsingularity of their Schur matrix.

## Follow-up: leading regular operator and rank-one degeneration

A further independent read-only algebra review passed (H1)–(H5), conditional
on the displayed geometric separation, old residue-matrix invertibility,
and polar inverse hypotheses. Physical polar coefficients are analytic:
the possible inverse pole is supported on binary initial states, while the
initial-zero inverse rows are regular. The direct beta bounds include the
vanishing coordinate in matching old-state-zero rows.

Every cleared coefficient of the shorter source row vanishes at the
matching old base point. This makes the divided residue in (H2) regular
even when the old state is zero. Thus the feedback block is analytic, and
the valuation bounds justify the coefficient identity
`H_-3 = -B_0 O^-1 Z_-3`. In odd length, distinct initial-zero poles determine
the sparse constant polar coefficients; the extra omitted binary block
contributes its determinant. The inverse-transition limit then yields (H5).
Only terms with at most one old pole are discarded in that formula.

These are operator identities, not a rank or nonvanishing theorem. In the
recorded m=3 modular fixture the incoming matrix and its image both have
rank 21 of 27. The later support argument below supplies the matching
characteristic-zero upper bound at this length; no all-length rank law follows.

The same review checked (R1)–(R3). The common suffix contributes the claimed
power; the first two prefix coefficients are independent of the initial
row. The local three cubic and six quadratic classes are independent, but
the displayed cross-time relations prevent inferring global independence
from this local nine-column calculation. The note preserves that limitation.

## Follow-up: scalar interpolation and six generic pivots

The independent reviewer also checked (H6)–(H11). The pair functions satisfy
the base-point conditions and isolate their double residues. Removing them
leaves quadratic single-line residues with matching-point vanishing, then a
linear polynomial. The exact source identity, append-block recurrence and
four structural zero rows all check. The quotient dimension and support
bound therefore have algebraic proofs, rather than numerical evidence alone.

The six-pivot argument in (H13)–(H15) passes under its stated geometry
conditions. Four leading rows independently evaluate the two linear forms
at two points of their respective old lines. Their kernel consists of
constant multiples of those line equations. The two remaining rows vanish
on the entire leading matrix, and their first derivatives on that kernel
form a nonzero antidiagonal matrix. Thus the argument uses legitimate
kernel elimination. Invertibility of the common matrix makes the first
transition derivative invertible on zero-sum rows; distinct reciprocal
row denominators justify the generic final-component detection. The
empty-suffix case at length five is directly nonzero. The required finitely
many nonzero conditions can hold simultaneously at positive parameters.

This establishes six isolated columns in the auxiliary family for every
`m>=5`, and in the actual leading incoming operator for odd `m>=5`.
It does not establish independence of the other `9m-6` columns or
nonvanishing of the full regular determinant. The separate finite six-by-six
checks use last-block boundary rows, whereas this uniform proof uses rows
from blocks two, four and five.

The sharper support count was separately checked: all `6(m-1)` scalar pair
rows involving either of the first block's nonzero-state lines are supported
on at most six columns. Adding the complementary row count gives
`rank Z_-3 <= min(9m, 9*choose(m,2)-6m+12)` for odd m. Conversion to the
two vector coordinates at each pair preserves rank because the common row
`e_2 G^-1` is nonzero. At m=3 the upper bound is 21, attained by the saved
minors of the incoming and leading regular matrices. Their generic
characteristic-zero ranks are therefore 21 on the stated valid region.

The reviewer also checked the determinant-valuation consequences. At m=3,
the analytic matrix `epsilon^3 H` has constant rank at most 21, so its
27-column determinant has order at least six. The saved nonzero coefficient
at order -75, with the recorded precision and good reduction, proves exact
characteristic-zero valuation -75 at that fixture. At m=4 the entrywise
order bound and nonzero leading determinant similarly give exact order -108.
The m=2 order -24 remains modular-only. None of these conclusions is a Lean
certificate or an arbitrary-length independence theorem.
