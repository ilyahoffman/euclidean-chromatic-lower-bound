import HoffmanChromatic.CoordinateFactor
import HoffmanChromatic.SphericalLayer
import HoffmanChromatic.CoefficientRank

/-!
The complete finite inequality: no detector or factorization hypothesis is
left to the caller. The two alphabets have six or seven consecutive integer
values; all dimensions and all powers of two are quantified.
-/

namespace HoffmanChromatic

open scoped BigOperators

noncomputable def rankCount (Q n D : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (D+1), (D+1-k) *
    ((weightPolynomial (fun j : Fin Q => newtonExponent j.val))^n).coeff k

theorem layerDetector_rank_bound (Q : ℕ) (hQ : Q = 6 ∨ Q = 7) (L : ℤ) (n ell : ℕ) :
    (layerDetector (@intervalLetter Q L) n ell).rank ≤ rankCount Q n (2^ell-1) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let enc : Fin Q → ℤ := intervalLetter L
  let V := SphericalLayer enc n (2^ell)
  have hp : 0 < (2:ℕ)^ell := pow_pos (by norm_num) _
  have hex : ∀ x : V, ∃ r : ℕ, sqNorm (layerPoint x) = 2*(r:ℤ)+1 := by
    intro x
    exact layer_row_exponent (2^ell : ℕ) (layerPoint x) (layerPoint_level hp x)
  let r : V → ℕ := fun x => Classical.choose (hex x)
  have hr : ∀ x : V, sqNorm (layerPoint x) = 2*(r x:ℤ)+1 :=
    fun x => Classical.choose_spec (hex x)
  let d : V → F2Series := fun x => signedPower (r x : ℤ)
  let B : Fin Q → Fin Q → F2Series := fun i b => signedPower (-(enc i * enc b))
  have hB : ∀ i b, B i b = ∑ j : Fin Q, PowerSeries.X^newtonExponent j.val *
      (coordinateU L j i * coordinateW L j b) := coordinate_factorization Q hQ L
  have hm : layerDetector enc n ell = coefficientMatrix (2^ell-1)
      (fun x y : V => d x * (∏ i, B (x.val i) (y.val i)) * d y) := by
    ext x y
    change binaryDetector ell (rho (layerPoint x) (layerPoint y)).toNat =
      PowerSeries.coeff (ZMod 2) (2^ell-1)
        (signedPower (r x : ℤ) * (∏ i, signedPower (-(layerPoint x i * layerPoint y i))) *
          signedPower (r y : ℤ))
    rw [← row_series_identity (2^ell : ℕ) (layerPoint x) (layerPoint y)
      (layerPoint_level hp x) (layerPoint_level hp y) (r x) (r y) (hr x) (hr y)]
    have hn := (layer_rho_spec (2^ell : ℕ) (layerPoint x) (layerPoint y)
      (layerPoint_level hp x) (layerPoint_level hp y)).1
    have hh := signedPower_detector ell (rho (layerPoint x) (layerPoint y)).toNat
    rw [Int.toNat_of_nonneg hn] at hh
    exact hh.symm
  change (layerDetector enc n ell).rank ≤ _
  rw [hm]
  calc
    _ ≤ ∑ j : Fin n → Fin Q, (2^ell-1+1 - ∑ i, newtonExponent (j i).val) :=
      tensor_coefficient_rank_bound n (2^ell-1) (fun j : Fin Q => newtonExponent j.val)
        B (coordinateU L) (coordinateW L) hB (fun x : V => x.val) d d
    _ = rankCount Q n (2^ell-1) :=
      profile_sum_eq_weighted_coefficients (fun j : Fin Q => newtonExponent j.val) n (2^ell-1)

/-- The paper's finite coefficient bound, without division and valid also for empty layers. -/
theorem finite_chromatic_inequality (Q : ℕ) (hQ : Q = 6 ∨ Q = 7)
    (L : ℤ) (n ell k : ℕ) (hc : (unitDistanceGraph n).Colorable k) :
    ((weightPolynomial (fun j : Fin Q => letterWeight (intervalLetter L j)))^n).coeff
      (2 * 2^ell-1) ≤ k * rankCount Q n (2^ell-1) := by
  calc
    _ ≤ k * (layerDetector (@intervalLetter Q L) n ell).rank :=
      spherical_layer_card_bound (intervalLetter L) (intervalLetter_injective Q L) n ell k hc
    _ ≤ k * rankCount Q n (2^ell-1) :=
      Nat.mul_le_mul_left k (layerDetector_rank_bound Q hQ L n ell)

end HoffmanChromatic
