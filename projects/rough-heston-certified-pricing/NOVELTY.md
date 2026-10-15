# Novelty and premise audit — 2026-10-15

## Versioned primary sources

1. Ben Hammouda–Ben Romdhane–Samet–Tempone, [arXiv:2609.00438v1](https://arxiv.org/html/2609.00438v1), 2026-08-31; no later version listed. Eq. (13) defines the trapezoidal exponent, Assumptions 3–5 are frequency-wise, Eq. (20) includes every level, Conjecture 1 asks for global domination, and Proposition 2 is conditional. Appendix H is a finite-frequency/finite-level experiment. The paper explicitly leaves global decay unproved.
2. Boyarchenko–Levendorskii, [arXiv:2508.15080v3](https://arxiv.org/html/2508.15080v3), 2026-06-30 (earlier versions 2025-08-20/25). Current title includes “II”; the target paper cites an earlier author list. Section 2.4.4/Figs. 2–3 already discuss large-frequency failures at inadequate time resolution, including growth of the computed exponent; §4 discusses Gauss–Laguerre reliability. Appendix A and Eqs. (2.15)–(2.19) distinguish several modified/iterated/implicit schemes. General instability is preempted.
3. Bayer–Breneis, [arXiv:2309.07023v1](https://arxiv.org/pdf/2309.07023), 2023-09-13; no later arXiv version listed. Theorem 2.2 bounds characteristic-function errors for kernel-based Markovian approximations; Theorem 2.7 and Remark 2.8 convert Fourier decay to weak errors. Corollaries 2.12/2.14 address smooth compactly supported/Lipschitz payoffs. These are genuine model transforms and kernel error, not explicit fixed-step PECE transforms. Truncation and error balancing are prior art.
4. Dastgerdi–Bastani (2020), SIAM J. Financial Math. 11(4), 1063–1097, [DOI 10.1137/19M1269324](https://epubs.siam.org/doi/abs/10.1137/19M1269324). Publisher abstract identifies Adams stability/convergence problems. Search-indexed manuscript text mentions high-frequency failures and Appendix B conditional stability, but full text was inaccessible; detailed claims require verification.
5. [RIDGE, arXiv:2607.25199v2](https://arxiv.org/html/2607.25199v2), 2026-07-30: quadratic implicit corrector as stabilization. Generic implicit/adaptive repair is not new.
6. El Euch–Rosenbaum, [arXiv:1609.02108v1](https://arxiv.org/html/1609.02108v1), §5.1 Eqs. (26)–(27): primary recovery of the standard single-correction Adams recurrence. The main 2026 paper cites this implementation reference but does not publish its own weights/correction count.

## Precise checked contribution and novelty limits

For the explicitly specified standard single-correction reference recurrence and the target paper's specified trapezoidal exponent, the Lean project proves exact degree 4^M and positive leading real coefficient of the final node for every finite M; derives degree 2·4^M and positive leading coefficient of the real exponent; deduces nonintegrability of the call-weighted modulus error against a bounded transform. This establishes an all-finite-mesh deterministic obstruction, including every proposed fixed refinement threshold.

No matching public resolution found as of 2026-10-15 in the searches performed. This is a provisional novelty assessment, not proof of novelty. We do not claim novelty for high-frequency Adams instability, adaptive refinement, implicit correction, Fourier truncation, or kernel weak-error bounds.

## Logical scope

One nonintegrable fixed-level summand forces failure of domination over all levels. However, proving that a standard reference implementation has this property does not verify the authors' unpublished source code or all antecedents of a conditional conjecture. A global-contour stability premise would itself fail. Frequency-wise convergence can coexist with divergence at infinity for each fixed mesh. Nonintegrability of a complex modulus does not automatically imply nonintegrability of its oscillating real part. Moment admissibility and the financial bridge remain separate proof obligations.

## Search coverage and limitations

Explorers searched exact identifiers/titles, domination/integrability, fixed-mesh instability, polynomial degree, 4^M, positive leading coefficients, author pages, GitHub, and indexed X/Twitter results. No relevant exact-paper GitHub or X result was found. No author was contacted. Unindexed/private repositories, inaccessible publisher full text, and all historical variants were not exhaustively reviewed. Search results are leads; mathematical claims above rely on the cited primary sources or are clearly marked candidates.
