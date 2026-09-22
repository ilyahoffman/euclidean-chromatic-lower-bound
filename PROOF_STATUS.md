# Proof coverage

This status applies to the source files and pinned dependencies in this
release. **All three asymptotic results of the extended abstract are proved.**

## Verified finite chain

| Mathematical step | Lean location / principal theorem | Status |
|---|---|---|
| Integer midpoint identity and distance bound | `Geometry.lean`: `distance_decomposition`, `layer_rho_spec` (all names are in namespace `HoffmanChromatic`) | Proved |
| Quarter-centred sphere identity | `Geometry.lean`: `quarter_sphere_identity` | Proved |
| Odd squared norm and integer row exponents | `Geometry.lean`: `layer_row_exponent`, `row_exponent_identity` | Proved |
| Detector on the entire interval 0 ≤ h < 2P, P a power of two | `Detector.lean`: `binaryDetector_spec` | Proved for all powers |
| Exact minimal index for arbitrary positive P, in both binomial bases | `DetectorIndex.lean`: `minimum_detector_index_iff`, `minimum_shifted_detector_index_iff` | Proved for every P ≥ 1 |
| Principal submatrix / colour-class rank bound | `RankColoring.lean`: `card_le_colors_mul_rank` | Proved over every field |
| Correct Euclidean scaling | `EuclideanBridge.lean`: `scaledPoint_unit_distance` | Proved |
| Actual detector on the spherical layer | `SphericalLayer.lean`: `spherical_layer_card_bound` | Proved |
| Whole-layer coefficient count | `Counting.lean`: `layer_card_eq_coefficient` | Proved |
| Surviving coefficient slots equal the weighted coefficient sum | `Counting.lean`: `profile_sum_eq_weighted_coefficients` | Proved |
| General coefficient-rank transfer | `CoefficientRank.lean`: `coefficient_rank_transfer` | Proved over every field |
| Tensor expansion and absorption of row/column series | `CoefficientRank.lean`: `tensor_coefficient_rank_bound` | Proved |
| Explicit Newton factorizations for Q = 6, 7 | `NewtonData.lean`: `newton_factor_6`, `newton_factor_7` | Proved as formal polynomial identities |
| Negative powers, detector coefficient, and row factors | `SeriesBridge.lean`: `signedPower_detector`, `row_series_identity` | Proved |
| Translated consecutive coordinate alphabets | `CoordinateFactor.lean`: `coordinate_factorization` | Proved for every integer translation |
| Concrete rank bound with no factorization premise | `FiniteBound.lean`: `layerDetector_rank_bound` | Proved |
| Complete finite coefficient inequality | `FiniteBound.lean`: `finite_chromatic_inequality` | Proved |
| Exact four polynomials and positive denominator | `Alphabets.lean` | Proved |
| Quotient lower bounds for Euclidean colourings | `finite_six_real`, `finite_seven_real` | Proved for every n and every power of two |

The explicit coordinate factorizations are sufficient for both alphabets used
in the paper. This release does not separately prove the general valuation
formula for arbitrary alphabet size. It proves the required instances directly.

## Closed asymptotic chains

| Step | Lean module / theorem | Status |
|---|---|---|
| A type contributes its multinomial coefficient to the whole layer | `MultinomialCount.lean` | Proved |
| Uniform logarithmic Stirling error, including zero multiplicities | `StirlingBounds.lean`, `UniformEntropy.lean` | Proved |
| Fixed-type logarithmic growth and exact Gibbs entropy identity | `MultinomialRate.lean` | Proved |
| Elementary generating-function bound for the weighted denominator | `CoefficientEstimates.lean` | Proved |
| Exponential margin absorbs polynomial losses | `TypeGrowth.lean` | Proved |
| Bounded coordinate padding realizes power-of-two levels | `TypeChromatic.lean` | Proved |
| Exact rational Gibbs type at 131/200 | `Subsequence.lean` | Proved |
| Full infinite-subsequence endpoint | `subsequence_chromatic : SubsequenceTarget` | **Proved** |
| Uniform entropy estimate for every integer type | `UniformEntropy.lean` | Proved |
| Entropy concavity at fixed total mass and homogeneous interpolation | `UniformEntropy.lean` | Proved |
| Euclidean dimension monotonicity and dyadic cover | `DimensionCover.lean` | Proved |
| All four integer witnesses imply logarithmic score bounds | `HandTypes.lean` | Proved |
| Interpolated types cover every relevant integer layer level | `MixedCover.lean` | Proved |
| Full eventual uniform rounded endpoint | `rounded_chromatic : RoundedTarget` | **Proved** |

The rounded proof uses the seven-letter alphabet for all four comparisons.
The first two comparisons are recomputed exactly with E7 instead of E6 and
remain strictly greater than 5/4. This is a deliberate proof simplification;
the article's original E6 comparisons are also retained and verified.

The subsequence proof clears the Gibbs denominator and uses fixed integer
multiplicities. Neither rounded endpoint uses the local coefficient
lemma, which is now proved separately. All geometric, rank, counting, arithmetic and limiting steps are in
the transitive proof dependencies.

## Closed sharp endpoint

| Obligation | Status |
|---|---|
| Uniform upper and lower coefficient bounds with matching n^(-1/2) factors | **Proved** in `UniformCoefficient.lean` |
| Uniform binomial lower bound in a central window | **Proved** in `BinomialWindow.lean` |
| Unrestricted binomial upper bound and location of a mode | **Proved** in `BinomialMode.lean` |
| Polynomial coefficient conditioning identity and uniform probability bounds | **Proved** in `MixturePolynomial.lean`, `MixtureLower.lean`, and `MixtureUpper.lean` |
| Attainment, uniqueness and compact bounds for minimizing parameters | **Proved** in `GibbsRate.lean`, `SaddlePoint.lean` and `UniformRate.lean` |
| Weighted denominator estimate and cancellation of n^(-1/2) | **Proved** in `WeightedCoefficient.lean` and `CoefficientRatio.lean` |
| Uniform rate bounds for both actual Euclidean graph families | **Proved** in `UniformRate.lean` with no unproved analytic premises |
| Existence and bracketed uniqueness of a_* | **Proved** in `SharpCrossing.lean` |
| Rational logarithm enclosures and the four crossing rows | **Proved** in `LogEnclosure.lean` and `SharpCertificates.lean` |
| All six interior endpoint bounds | **Proved** in `InteriorCertificates.lean` |
| Four concave functions covering [a_*,2a_*] | **Proved** in `RateCover.lean` and `SharpCover.lean` |
| Final bound c*C_*^d with a positive constant independent of d | **Proved**: `uniform_chromatic : UniformTarget` |

`UniformTarget` is now inhabited by a closed proof term. Its definition
requires the crossing, its bracketed uniqueness, the numerical enclosure,
and the chromatic estimate in every sufficiently large dimension.

The standalone minimal-detector-index remark in the longer paper is now
proved for all positive P, including both binomial bases. The proof uses
binomial inversion, the binary Lucas identity, and a degree-preserving change
of basis. No enumeration of periods is used. This extra result is independent
of the three closed endpoint proofs.

The general-Q valuation argument is replaced by exact polynomial
factorizations for the required Q = 6 and 7. A separate arbitrary-Q theorem,
explicit numerical values of c and d0, and an eleven-decimal enclosure of
C_* are not claimed. None is a missing premise of the three stated endpoints.

`DirectStatements.lean` also proves all three endpoints with the Euclidean
metric and arbitrary colouring functions written out explicitly. The two
rate functions there use the four displayed polynomials directly.

## Recorded verification

The aggregate project and every mathematical declaration are checked by
`tools/verify.py`. Discovery is by source module, so private declarations,
definitions and generated equations are included. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed in the transitive dependency
closure. Compiler runtime declarations are excluded only after checking
that the mathematical closure does not depend on them.

See `verification/RESULT.txt` for the count, `verification/axioms.log` for
the discovered declarations, and `verification/statements.log` for the
endpoint signatures. Counts of generated equations are not counts of
independent mathematical results. Clean dependency checks, warning-free
compilation, witness regeneration and independent arithmetic replay are
mandatory parts of the recorded verification.
