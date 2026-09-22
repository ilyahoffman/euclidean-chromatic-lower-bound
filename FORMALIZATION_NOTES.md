# Mathematical routes used in the Lean proofs

Mathematical author: Ilya Hoffman  
Email: ilya.hoffman@gmail.com  
ORCID: https://orcid.org/0009-0008-9083-2105

The finite geometric construction and coefficient-rank argument are those of
the English spherical-layer article. The two rounded asymptotic endpoints
use the alternative integer-type arguments below; the sharp endpoint follows
the uniform coefficient estimates. This note explains the proof terms;
it is not an additional trusted source for Lean.

## The common finite input

Write A = A7 and E = E7, with the polynomials defined in the article. For
P = 2^ell and every proper k-colouring of Euclidean n-space, Lean proves

    [t^(2P-1)] A(t)^n ≤ k S_n(P-1),
    S_n(D) = sum_{j=0}^D (D+1-j) [s^j] E(s)^n.

For 0 < s ≤ 1, positivity of the coefficients gives

    S_n(D) s^D ≤ (D+1) E(s)^n.

This elementary estimate loses a polynomial factor. That is harmless for
strict exponential margins, but insufficient for the exact C_* endpoint.

The seven coordinate weights, in the code's integer order -3,...,3, are
w = (21,10,3,0,1,6,15). For an integer type m, set

    M(m) = sum_i m_i,
    K(m) = sum_i w_i m_i,
    H(m) = M(m) log M(m) - sum_i m_i log m_i.

A type contributes multinomial(m) points to the coefficient of degree K(m)
in A^M(m). Appending r coordinates with value 1 gives at least the same
number of points in degree K(m)+r of A^(M(m)+r). The injection is proved
through polynomial coefficient inequalities.

Stirling's theorem in mathlib yields two separate proved estimates:

1. For each fixed m,
   log multinomial(qm) / q tends to H(m).
2. For every m on this fixed seven-letter alphabet,
   log multinomial(m) ≥ H(m) - B(log(M(m)+1)+1),
   with one constant B independent of m, including types with zero entries.

The two rounded proofs do not use the local coefficient lemma.

## Infinitely many dimensions: 1.316^d

Put t = 131/200 and m_i = 131^(w_i) 200^(21-w_i). These are fixed positive
integers, and m_i = 200^21 t^(w_i) exactly. Consequently

    H(m) = M(m) log A(t) - K(m) log t.

Lean checks by rational arithmetic that A(t) > (329/250) E(t^2).
For every large power of two P, divide 2P-1 = q K(m) + r with 0 ≤ r < K(m).
The type qm followed by r ones lies in the required layer of dimension
n = q M(m)+r. The finite bound then gives

    multinomial(qm) t^(qK(m)+r) ≤ k P t E(t^2)^n.

The positive logarithmic margin
M(m) log(A(t)/((329/250) E(t^2))) absorbs the factor P and the bounded
remainder r. Uniformity over remainders follows from finiteness; Lean does
not enumerate the enormous set of possible remainders. Taking larger powers
of two produces dimensions above every prescribed N. This proves
`subsequence_chromatic : SubsequenceTarget`.

The resulting existential dimension threshold is intentionally not an
explicit numerical estimate. The original subsequence assertion is also
existential.

## Every sufficiently large dimension: 1.30^d

In the same coordinate order, use

    u = (0,0,21,112,63,4,0),
    v = (0,1,28,100,64,7,0),
    z = (0,4,33,86,62,14,1).

All three masses are 200, and their energies are 150, 200 and 300.
Define the logarithmic score

    F(m;s) = H(m) + (K(m)/2) log s - M(m) log E(s).

The four exact integer comparisons prove

    F(u;3/8), F(v;3/8), F(v;12/25), F(z;12/25)
      > 200 log(13/10) + log(5/4).

The first two comparisons use E7 here, whereas the printed article uses E6.
They remain valid; the Lean proof recomputes them exactly. Using one alphabet
simplifies interpolation and changes none of the endpoint statements.

Entropy is homogeneous and concave on vectors of equal total mass.
Thus for 0 ≤ j ≤ q, both mixtures (q-j)u+jv and (q-j)v+jz have score at least
q(200 log(13/10)+log(5/4)) with the corresponding s. Their energies advance
in steps of 50 and 100. Division with remainder therefore realizes every
integer level from 150q to 300q+1 after appending fewer than 100 ones.

For any q > 0, the least suitable power of two supplies a level
2P-1 in this interval. Given a sufficiently large ambient dimension d, take
q = floor((d-100)/200). Every constructed dimension n = 200q+r is at most d,
and d ≤ 200q+300. Zero extension is an explicitly proved Euclidean isometry.

The uniform multinomial estimate, the finite rank bound, and P ≤ 150q+1 give

    log k ≥ 200q log(13/10) + q log(5/4) - O(log q) - O(1).

All constants are uniform over the two choices of s and the fewer than 100
extra coordinates. The positive linear term q log(5/4) absorbs both losses
and the at most 300 omitted ambient coordinates. The formal theorem is
`rounded_chromatic : RoundedTarget`, with quantifiers over every d ≥ d0.

## Verified binomial ingredients for the sharp endpoint

The additional modules `BinomialEntropy.lean`, `BinomialWindow.lean` and
`BinomialMode.lean` prove the following facts without extra assumptions:

- The Bernoulli divergence D(u||t) is nonnegative and at most
  (u-t)^2/(t(1-t)) for 0 < u,t < 1.
- For u = k/n with 0 < k < n, the difference between
  log binomialMass(n,k,t) and -n D(u||t) - (1/2) log(nu(1-u))
  has an absolute bound independent of n, k and t.
- For a > 0 and A ≥ 0, positive constants c,C and N exist such that
  c ≤ sqrt(n) binomialMass(n,k,t) ≤ C whenever n ≥ N,
  a ≤ t ≤ 1-a and |k-nt| ≤ A sqrt(n).
- A mode lies within distance one of nt. Therefore the upper bound holds
  for every index k, uniformly over t in the same compact interval.

The conditional averaging argument is now also formalized. `FiniteLaw.lean`
and `FiniteProduct.lean` prove the finite weighted-sum identities, moments
of independent sums, and Chebyshev's inequality. In `MixturePolynomial.lean`,
each record contributes exactly a shifted power of the Bernoulli polynomial.
Its coefficient is a binomial mass, including zero at negative indices.

`MixtureUpper.lean` bounds the exceptional event N_01 < a*n/2 by O(1/n).
`MixtureLower.lean` proves that, for large n, an event of mass at least 1/2
has N_01 >= a*n/2 and |R+theta*N_01-m| <= D*sqrt(n). The central binomial
bound applies on that event. Constants are chosen before both n and the
sample-space type, preserving uniformity when the record space grows.

`TiltedPolynomial.lean` identifies the mixture polynomial with
Z(x)^(-1) Z(x*u). Thus `uniform_coefficient_bounds` proves the article's
upper bound at every coefficient and its lower bound within distance one
of the mean. The summation of (r+1)*s^r and cancellation of the common
square-root factor are proved in `WeightedCoefficient.lean` and
`CoefficientRatio.lean`. `SharpParameters.lean` connects these estimates
to both actual Euclidean graph families, with no unproved analytic estimate
as a premise. The saddle parameters are constructed in `SaddlePoint.lean`.

## The sharp endpoint

The matching coefficient estimates give the exact constant-prefactor bound.
`GibbsRate.lean` proves that the derivative of the tilted mean with respect
to the logarithmic parameter is a positive variance. Supporting lines prove
the global minimum property. `SaddlePoint.lean` identifies the infimum in
`Targets.lean` with that attained value. Common bounds 1/4 < t,s < 4/5
are checked for the full interval 0.37 <= delta <= 0.75.

`RateConcavity.lean` proves nonemptiness and boundedness below of the sets
whose infima occur in the rate definitions, then proves concavity and
continuity. `RateBracket.lean` proves both the finite minimum enclosure and
the slope bounds for changes in the mean. These slope bounds establish
crossing monotonicity without differentiating the inverse mean function.

For logarithms, `LogEnclosure.lean` applies the proved Taylor remainder to
eta=(x-1)/(x+1) and -eta. The resulting rational remainder is slightly looser
than the article's bound and is still sufficient. The generator uses exact
rational arithmetic to propose witnesses. Lean proves every logarithm bound,
minimum bound, crossing row, and interior endpoint inequality. No generated
data is accepted without a proof.

`SharpCrossing.lean` proves existence and bracketed uniqueness of a_* and
1.309251 < exp(delta6(a_*)) < 1.309252. `SharpCover.lean` applies the four
concave minorants and all six interior bounds to cover [a_*,2a_*]. The least
power of two above a_* n lies in that interval after division by n.
`Uniform.lean` combines the two uniform constants and proves
`uniform_chromatic : UniformTarget` with the actual Euclidean metric.

## Why powers of two: the exact minimal detector index

For every positive integer P, prescribe f(h) = 1 at h = 0 and h = P, and
f(h) = 0 at the other integers in 0 <= h < 2P. Work over F2.
`DetectorIndex.lean` proves

    D_min(P) = P-1     if P is a power of two,
             = 2P-1  otherwise.

The statement is an equivalence: an expansion using indices at most D exists
on the entire window if and only if D_min(P) <= D. It is proved separately
for the bases choose(h,j) and choose(h-1,j). At h = 0 the latter has the
generalized value choose(-1,j) = (-1)^j = 1 in F2.

The proof has four steps. Substituting X+1 twice in a polynomial proves that
the binary Pascal transform is its own inverse. Thus the forced coefficients
are a_j = 1 + choose(j,P). Lucas reduction, together with the evenness of the
nontrivial central binomial coefficients, proves that choose(2P-1,P) is odd
exactly for powers of two. This gives the sharp obstruction at index 2P-1
in the other cases; for powers of two the coefficient at P-1 is one and the
existing detector realizes that index. Finally, the identities

    choose(h-1,j) = sum_{i=0}^j choose(h,i),
    choose(h,j+1) = choose(h-1,j) + choose(h-1,j+1)

hold as functions on all nonnegative h in F2, including h = 0. They show
that the spans of the two bases through any index D coincide.

The Lean definitions use these finite-dimensional spans, which are precisely
the allowed finite linear combinations. The theorem concerns the prescribed
detector on the full window; it makes no optimality assertion about other
detectors, smaller distance sets, or the eventual chromatic bounds.
