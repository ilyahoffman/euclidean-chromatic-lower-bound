# Hoffman chromatic bounds in Lean 4

**Status: all three results of the extended abstract are proved in Lean,
through the actual Euclidean graph, including the exact constant-prefactor
bound `c * C_*^d`.**

The closed endpoint theorems are:

- `HoffmanChromatic.rounded_chromatic`: `1.30^d` in every sufficiently large dimension;
- `HoffmanChromatic.subsequence_chromatic`: `1.316^d` in arbitrarily large dimensions.
- `HoffmanChromatic.uniform_chromatic`: `c * C_*^d` in every sufficiently large
  dimension, where `c > 0` is independent of the dimension, the crossing defining
  `C_*` is unique in the stated bracket, and `1.309251 < C_* < 1.309252`.

All three statements are proved from the actual Euclidean unit-distance graph,
without unproved coefficient estimates, numerical enclosures or asymptotic
hypotheses. Their exact endpoint specifications are in `Targets.lean`, and
`Statements.lean` checks that the corresponding proof terms inhabit them.

Mathematical author: **Ilya Hoffman**  
Email: ilya.hoffman@gmail.com  
ORCID: https://orcid.org/0009-0008-9083-2105

This project formalizes the final spherical-layer paper accompanying
`HOFFMAN_CHROMATIC_EXTENDED_ABSTRACT_EN_20260916.zip`. The intended scope is
the entire proof of those results, including the uniform constant-prefactor
bound and the stronger bound on infinitely many dimensions. Version 1.1.0
also proves the article's minimal-detector-index remark for every positive
period and strengthens the reproducibility checks. The Lean implementation was prepared
with Codex assistance.

## What has been proved

For Q = 6 and Q = 7, Lean proves, for every dimension n and every power of two
P = 2^ell, that every proper colouring of Euclidean n-space with k colours satisfies

\[
[t^{2P-1}]A_Q(t)^n\;\le\;
k\sum_{j=0}^{P-1}(P-j)[s^j]E_Q(s)^n.
\]

The four polynomials are exactly

\[
\begin{aligned}
A_6(t)&=1+t+t^3+t^6+t^{10}+t^{15},& A_7(t)&=A_6(t)+t^{21},\\
E_6(s)&=1+s+s^3+s^4+s^8+s^9,& E_7(s)&=E_6(s)+s^{11}.
\end{aligned}
\]

The denominator is proved positive. The real quotient bounds are the theorems
`HoffmanChromatic.finite_six_real` and `HoffmanChromatic.finite_seven_real`
in `HoffmanChromatic/Alphabets.lean`.

These theorems include the whole finite chain: the integer layer, its distance
window, parity, the binary detector, the explicit coordinate factorization,
tensor expansion, coefficient-rank transfer, vertex counting, and the passage
to Euclidean colourings. No rank estimate or factorization is an unproved
premise of these two theorems. In fact, the finite statements also cover n = 0
and P = 1; the article only needs positive dimension and P at least 2.

Separate theorems verify the four exact rational comparisons with denominator
M = 200 and the exact inequality
`A7(131/200) / E7((131/200)^2) > 329/250`.
Their links to the two asymptotic endpoints are now also proved. The Lean
proofs use direct multinomial estimates and explicit integer types; they do
not depend on the article's sharper local coefficient lemma. The mathematical
changes of route are documented in `FORMALIZATION_NOTES.md`.

## The sharp endpoint

`UniformTarget` specifies the sharp constant-prefactor bound, together with
the defining crossing, its uniqueness in the stated bracket, and
`1.309251 < C_* < 1.309252`. It is proved by `uniform_chromatic` in
`Uniform.lean`. The uniform inverse-square-root coefficient estimate, the weighted
denominator estimate, and their application to both Euclidean graph families
are now proved in `UniformCoefficient.lean`, `WeightedCoefficient.lean`, and
`SharpParameters.lean`. `GibbsRate.lean` and `SaddlePoint.lean` prove the
attained minima and uniqueness. `UniformRate.lean` connects these minima to
both Euclidean graph families. `SharpCertificates.lean` and
`InteriorCertificates.lean` check the finite rational bounds using a proved
logarithmic remainder. `SharpCrossing.lean`, `SharpCover.lean` and
`Uniform.lean` complete the crossing, covering, and dimension arguments.

The exact constant is defined by its unique crossing, not by a floating-point
number. The formal numerical enclosure has six decimal places. Constants and
dimension thresholds are existential, as in the final extended abstract.

`DirectStatements.lean` independently writes out the three endpoints using
arbitrary colouring functions, Euclidean distance, and the four explicit
polynomials. Its proofs connect those statements to the main theorems.
Thus readers can inspect the conclusion without unfolding the project's
graph or rate abbreviations.

`DetectorIndex.lean` proves the separate minimal-index remark for every
positive P: the least index is P-1 when P is a power of two, and 2P-1 otherwise.
Both binomial bases in the article are covered. This is a theorem about the
prescribed detector on the entire integer window, not a claim of optimality
among all possible geometric constructions or rank methods.

The necessary Newton factorizations for Q = 6 and 7 are proved directly as
polynomial identities; a separate general-Q valuation theorem is unnecessary
for these results. See `PROOF_STATUS.md` for the exact scope.

## Reproduce the checks

The project pins Lean **4.19.0** and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0).
Install Lean through elan, then run from this directory:

```sh
python3 tools/fetch_cache.py
python3 tools/verify.py --clean
```

Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` together.
Do not update mathlib to a different revision before reproducing this release.
The first command downloads the precompiled dependencies needed by the
project. The second removes the project's own build cache and rebuilds every
project module. It checks the toolchain and clean dependency revisions,
regenerates all three witness files in a temporary directory, and replays
the printed arithmetic independently. Every Lean warning fails the build.

`Audit.lean` discovers declarations by source module and checks their
transitive axiom dependencies, including private proofs and definitions.
The verifier also confirms that every project module is imported by the
audit. Compiler-generated runtime code is listed separately and must not
occur in the mathematical dependency closure.

For one command that also writes fresh logs and checks for prohibited proof
placeholders, use:

```sh
python3 tools/verify.py
```

A separate strict completion gate is available:

```sh
python3 tools/check_full.py
```

It checks actual proof terms for **all three endpoints**, including
`uniform_chromatic : UniformTarget`, and the exact detector-index formula
in both bases. It is also run by `tools/verify.py`.

The supplied `verification/` directory contains the successful build and audit
logs from this release. It is evidence of the recorded run; rerun the commands
above to verify the files independently.

The supplied `.github/workflows/verify.yml` runs the same checks from a
fresh checkout, without a GitHub build cache. Its actions are pinned by
commit; it follows the official [Lean action](https://github.com/leanprover/lean-action).
The workflow has not been run on a remote repository as part of this release.
`RELEASE_VERIFICATION.md` records the local reproduction actually performed.

## Trust and representation

- No `sorry`, `admit`, custom axiom declarations, `native_decide`, or
  `Lean.ofReduceBool` is used in project proofs.
- The audit accepts only Lean's usual `propext`, `Classical.choice`, and
  `Quot.sound` axioms. These are foundational dependencies, not additional
  assumptions about the chromatic bound.
- `norm_num` and `ring` produce proof terms checked by Lean. Python supplies
  explicit Newton and rational-logarithm witnesses; it is not trusted to
  certify them. The generated Lean sources suffice for verification.
- `NewtonData.lean` verifies polynomial identities in the formal variable.
  The finite case split concerns the entries of the two small coordinate
  matrices, not an enumeration of dimensions, colourings, or graph vertices.
- The ambient space is `EuclideanSpace ℝ (Fin n)`, with its L2 distance.
  It is not the sup-metric space on an ordinary function type.
- `ChromaticLowerBound n b` means that every finite proper colouring of the
  unit-distance graph uses at least b colours. This avoids an inappropriate
  conversion of an infinite chromatic number to a real number.
- All generating-function counts use natural-number coefficients. Only the
  detector and its rank computation use the field `ZMod 2`.

To read the proof as a geometer, start with `PROOF_STATUS.md`, then
`Geometry.lean`, `SphericalLayer.lean`, `FiniteBound.lean`, and `Alphabets.lean`.
The method itself is proved in `CoefficientRank.lean`; its concrete use is
proved in `SeriesBridge.lean` and `CoordinateFactor.lean`.

The original English article and extended abstract are included under
`reference/`. They identify the mathematical source; the successful endpoint
and dependency checks refer to the Lean proofs themselves.
