# Novelty audit — 15 October 2026

**No matching public proof found as of 15 October 2026** in the bounded searches
below. This is not a guarantee of priority. The four-period theorem has passed
complete formal verification; the broader structural theorem now also compiles
and passes its axiom and independent statement audits. Publication novelty
remains provisional.

## Source comparison

| Source and version | Assumptions and verified statement | Overlap and proposed delta |
|---|---|---|
| [Dano–Honoré–Weidner, arXiv:2610.17104v1](https://arxiv.org/html/2610.17104v1), 12 October 2026, §3.4, Conjecture 1, Appendix A | First-order dynamic multinomial logit, unrestricted alternative-specific effects, strictly exogenous covariates, fixed initial state. Equation (24) is a valid indexed family; equation (25) counts it. Q=3,T=4 has 33 proposed moments in 81 path coordinates. Appendix A leaves both independence and completeness open for Q>=3,T>=4. | The polynomial-kernel reformulation is inherited, not new. Candidate new content is an explicit geometric description of coefficient restrictions, an exact rank witness in an economic specification, and a structural horizon extension. |
| [DHW author draft](https://kevindano.github.io/assets/files/DHW_DynamicMultinomialLogit.pdf), 7 October 2026, Appendix A.3, printed p.41 | Same stated gaps as arXiv v1. | Earlier distinct version; no newer proof found on author page. |
| [Honoré–Weidner](https://academic.oup.com/restud/article/92/5/3112/7823637), Review of Economic Studies 92(5), 2025, §6 | Binary dynamic logit with fixed effects, lagged outcomes and strictly exogenous regressors. Constructs moments; discusses subsequent exact count results. | Binary construction and rank precedent; does not settle alternative-specific multinomial effects. |
| [Kruiniger, arXiv:2010.03382v5](https://arxiv.org/pdf/2010.03382v5), 3 February 2023, Appendix Lemma 1 | Binary AR(1), T>=3, nonzero state-dependence coefficient, fixed initial condition; probability-matrix rank argument, including almost-sure independence of selected columns. Also selected binary AR(2) cases. | Rank-certificate precedent, not a Q>=3 theorem. |
| [Dano author draft](https://kevindano.github.io/assets/files/JMP_KevinDano.pdf), 5 November 2025, Theorem 1 and Remark 6, pp.23–24 | Binary AR(1) exact rank under distinct time/lag indices; transition functions and partial fractions. Remark 6 reports numerical exhaustiveness of its multinomial construction at T=3 but not T>=4, referring wider construction to DHW. | Transition-probability construction does not prove the target completeness. This version differs from [arXiv:2303.00083v2](https://arxiv.org/abs/2303.00083), 4 December 2023. |
| [Dano supplement](https://kevindano.github.io/assets/files/JMP_KevinDano_SupplementalAppendix.pdf), §5 | Multinomial first-order dynamics, exogenous regressors, alternative-specific effects, independent type-I extreme-value shocks. | Valid moments, without the requested general rank/basis theorem. |
| [Mbakop, arXiv:2305.15691v1](https://arxiv.org/pdf/2305.15691v1), 25 May 2023 | Conditional moment inequalities characterizing identified sets in semiparametric panel multinomial models, computed by multiple-objective linear programs. | Computational identification framework, different assumptions and target from an exact basis of parametric logit moment equalities. |

[TSE's December 2025 seminar](https://www.tse-fr.eu/seminars/2025-dynamic-panel-multinomial-logit-models)
and [KU Leuven's February 2026 seminar listing](https://feb.kuleuven.be/research/decision-sciences-and-information-management/documents/seminars2ndsem2026.pdf)
use informal completeness language. They provide no proof. The later detailed
October manuscripts explicitly retain the conjecture; seminar abstracts cannot
establish that its proof exists.

## Search coverage and access limits

An independent literature explorer searched arXiv identifiers, the exact paper
title, multinomial completeness/conjecture terminology, author pages, RePEc
and GitHub-indexed results. The [RePEc record](https://ideas.repec.org/p/arx/papers/2010.03382.html)
confirms Kruiniger's revision. The [Dano research page](https://kevindano.github.io/research/)
supplied the author manuscripts above. Direct Scholar, OpenAlex works search and
GitHub code-search requests returned tool internal errors: these are inaccessible
searches, not negative findings.

A signed-in Chrome browser was available. A read-only X Latest search for
`"Dynamic Panel Multinomial Logit"` showed [this paper announcement](https://x.com/eBlogs/status/2110410084157186166)
and no matching proof in the displayed results. No private account information
is retained. No messages or posts were sent.

## CausalSmith bank

Inspected the untruncated repository tree at
`a7085d88d2e4b30003db7097ca374f4718da0f01`, saved in
`sources/causalsmith-tree.json`: one accepted entry, 1,388 downgraded entries,
303 failed entries. Relevant public digests are saved alongside the tree.
The sole accepted entry concerns latent causal-representation recovery from
interventions, not panel-logit likelihood rank; its README was read.

| Run | Scope and distinction |
|---|---|
| `panel_mnl_offdiag_moment_bounds_v1` (downgraded) | Three-choice three-wave panel, known coefficients and local neutral-persistence geometry. Corrected a false coefficient-robust rank claim. Does not prove this generic moment-basis conjecture. |
| `panel_mnl_offdiag_sharp_v1` (downgraded) | Three alternatives, two transitions, constant covariates and known stay multipliers; sharp intervention-transition regions. Records two unrepaired dual normalization/dependency defects. Not a clean proof of a matching result. |
| `panel_dynlogit_schedule_span_v1` (downgraded) | Binary homogeneous-index selected strata and known slopes; treatment-reordering identification via reduced poles. Relevant span methodology, different target. |
| `pid_felogit_hankel_honesty_v1` (downgraded) | Hausdorff/Hankel geometry and inference for AME bounds; unresolved minimax/attainment claims. Different moment geometry. |
| `pid_felogit_responder_sos_v1` (failed) | Local T=2 responder-envelope contact analysis; promised general finite characterization and constructive uniform procedure unfinished. |

Public provenance: [CausalSmith repository](https://github.com/Jiyuan-Tan/CausalSmith/tree/a7085d88d2e4b30003db7097ca374f4718da0f01/CausalSmith/doc/research/_bank).
Digest “proved” counts and Lean paths were not treated as independent proof
validation. This audit did not retrieve or verify every archived derivation.

## Precise proposed contribution

For three choices, identify six projective base points per post-initial time
block; construct separating polynomials and characterize the cleared-likelihood
span using their vanishing ideal. For four periods, additionally prove that the
particular 33 source moments are a basis using fixed, explicitly indexed minors
with a normalized scalar-covariate witness. A generic unrestricted-table result
does not alone transfer to the economic specification. The finite transfer now proves an explicit nonempty open dense region after
that substitution. The arbitrary-period transfer is also Lean checked: an explicit nonempty
open dense region in the joint normalized scalar-covariate economic domain
supports the complete moment-space dimension formula for every T>=1.

The finite case alone has unestablished publication value. Any broader rank
formula still needs a separate independence proof for equation (24)'s particular
family before claiming the entire arbitrary-horizon conjecture.
