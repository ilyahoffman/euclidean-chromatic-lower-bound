# Completed proof map

All three endpoint propositions are inhabited by closed Lean proofs. The
proof map below follows the mathematical dependencies of the sharp bound.
The exact scope and alternate proof routes are recorded in PROOF_STATUS.md
and FORMALIZATION_NOTES.md.

| Stage | Modules | Outcome |
|---|---|---|
| Euclidean layer and binary detector | Geometry, Detector, SphericalLayer, EuclideanBridge | A genuine unit-distance graph and its detecting matrix |
| Rank transfer and coordinate factorization | CoefficientRank, NewtonData, SeriesBridge, CoordinateFactor | Kernel-checked rank bound for Q = 6, 7 |
| Exact counts and finite quotient | Counting, FiniteBound, Alphabets | Chromatic coefficient quotient in every dimension |
| Binomial estimates | StirlingBounds, BinomialEntropy, BinomialWindow, BinomialMode, BinomialPolynomial | Uniform central lower and unrestricted upper bounds |
| Conditioning and finite probability | FiniteLaw, FiniteProduct, MixturePolynomial, MixtureUpper, MixtureLower | Exact coefficient mixture with uniform estimates |
| Polynomial coefficients and cancellation | TiltedPolynomial, UniformCoefficient, WeightedCoefficient, CoefficientRatio | Matching inverse-square-root factors cancel |
| Attained rate functions | GibbsRate, SaddlePoint, RateConcavity, RateBracket, UniformRate | Unique minimizers and uniform constant-prefactor rate bounds |
| Exact arithmetic | LogEnclosure, SharpCertificates, InteriorCertificates | Four crossing rows and six interior endpoint bounds |
| Sharp base | RateCover, SharpCrossing, SharpCover | Unique crossing, six-decimal enclosure and full interval cover |
| Every large dimension | Uniform | uniform_chromatic : UniformTarget |
| Explicit colouring formulations | DirectStatements | All three endpoints with the Euclidean metric and polynomials written out |
| Detector-index remark | DetectorIndex | Exact least index for every positive P, in both bases |

The two additional endpoints use the direct integer-type arguments:

- Rounded.lean: rounded_chromatic : RoundedTarget.
- Subsequence.lean: subsequence_chromatic : SubsequenceTarget.

## Completion gates

`tools/check_full.py` requires actual proof terms for all three endpoints and
the detector-index equivalence in both bases. `tools/verify.py` checks clean
pinned dependencies, regenerates witnesses, rebuilds the project, audits all
declarations and their transitive axiom dependencies, checks the signatures,
and replays the article's arithmetic independently.

The only permitted axioms are propext, Classical.choice, and Quot.sound.
Generated arithmetic witnesses are proved by Lean, not accepted as certificates
on the authority of Python or floating-point computation.

## Separate material in the longer paper

The standalone minimal-index statement is now proved, although it is not an
endpoint dependency. The general-Q valuation argument is replaced by direct
proofs of the two required Newton factorizations. See PROOF_STATUS.md for the
precise scope and numerical precision.
