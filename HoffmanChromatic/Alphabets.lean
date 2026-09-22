import HoffmanChromatic.FiniteBound

/-! The finite chromatic inequalities with precisely the four polynomials in the paper. -/

namespace HoffmanChromatic

open scoped BigOperators
open Polynomial

noncomputable def countA6 : Polynomial ℕ := 1+X+X^3+X^6+X^10+X^15
noncomputable def countA7 : Polynomial ℕ := countA6+X^21
noncomputable def countE6 : Polynomial ℕ := 1+X+X^3+X^4+X^8+X^9
noncomputable def countE7 : Polynomial ℕ := countE6+X^11

theorem alphabet_six_count :
    weightPolynomial (fun j : Fin 6 => letterWeight (intervalLetter (-2) j)) = countA6 := by
  simp only [weightPolynomial, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change X^10 + (X^3 + (X^0 + (X^1 + (X^6 + (X^15 + 0))))) = countA6
  unfold countA6
  ring

theorem alphabet_seven_count :
    weightPolynomial (fun j : Fin 7 => letterWeight (intervalLetter (-3) j)) = countA7 := by
  simp only [weightPolynomial, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change X^21 + (X^10 + (X^3 + (X^0 + (X^1 + (X^6 + (X^15 + 0)))))) = countA7
  unfold countA7 countA6
  ring

theorem rank_six_count :
    weightPolynomial (fun j : Fin 6 => newtonExponent j.val) = countE6 := by
  simp only [weightPolynomial, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change X^0 + (X^1 + (X^3 + (X^4 + (X^8 + (X^9 + 0))))) = countE6
  unfold countE6
  ring

theorem rank_seven_count :
    weightPolynomial (fun j : Fin 7 => newtonExponent j.val) = countE7 := by
  simp only [weightPolynomial, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change X^0 + (X^1 + (X^3 + (X^4 + (X^8 + (X^9 + (X^11 + 0)))))) = countE7
  unfold countE7 countE6
  ring

noncomputable def weightedCount (E : Polynomial ℕ) (n D : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (D+1), (D+1-k) * (E^n).coeff k

theorem finite_six (n ell k : ℕ) (hc : (unitDistanceGraph n).Colorable k) :
    (countA6^n).coeff (2*2^ell-1) ≤ k * weightedCount countE6 n (2^ell-1) := by
  have h := finite_chromatic_inequality 6 (Or.inl rfl) (-2) n ell k hc
  simpa only [alphabet_six_count, rankCount, rank_six_count, weightedCount] using h

theorem finite_seven (n ell k : ℕ) (hc : (unitDistanceGraph n).Colorable k) :
    (countA7^n).coeff (2*2^ell-1) ≤ k * weightedCount countE7 n (2^ell-1) := by
  have h := finite_chromatic_inequality 7 (Or.inr rfl) (-3) n ell k hc
  simpa only [alphabet_seven_count, rankCount, rank_seven_count, weightedCount] using h

theorem weightedCount_pos (E : Polynomial ℕ) (hE : E.coeff 0 = 1) (n D : ℕ) :
    0 < weightedCount E n D := by
  have hp : (E^n).coeff 0 = 1 := by
    rw [← Polynomial.constantCoeff_apply, map_pow, Polynomial.constantCoeff_apply, hE, one_pow]
  have h := Finset.single_le_sum (s := Finset.range (D+1))
    (f := fun k => (D+1-k) * (E^n).coeff k) (fun k _ => Nat.zero_le _)
    (show 0 ∈ Finset.range (D+1) by simp)
  simp only [Nat.sub_zero, hp, mul_one] at h
  exact lt_of_lt_of_le (Nat.succ_pos D) h

/-- The quotient form of the finite bound, expressed directly for Euclidean colourings. -/
theorem finite_six_real (n ell : ℕ) : ChromaticLowerBound n
    (((countA6^n).coeff (2*2^ell-1) : ℝ) / (weightedCount countE6 n (2^ell-1) : ℝ)) := by
  have hE : countE6.coeff 0 = 1 := by norm_num [countE6]
  have hp : 0 < (weightedCount countE6 n (2^ell-1) : ℝ) := by
    exact_mod_cast weightedCount_pos countE6 hE n (2^ell-1)
  intro k hc
  apply (div_le_iff₀ hp).2
  exact_mod_cast finite_six n ell k hc

theorem finite_seven_real (n ell : ℕ) : ChromaticLowerBound n
    (((countA7^n).coeff (2*2^ell-1) : ℝ) / (weightedCount countE7 n (2^ell-1) : ℝ)) := by
  have hE : countE7.coeff 0 = 1 := by norm_num [countE7, countE6]
  have hp : 0 < (weightedCount countE7 n (2^ell-1) : ℝ) := by
    exact_mod_cast weightedCount_pos countE7 hE n (2^ell-1)
  intro k hc
  apply (div_le_iff₀ hp).2
  exact_mod_cast finite_seven n ell k hc

end HoffmanChromatic
