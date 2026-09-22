import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.Card

/-!
The generating-function count of the entire layer, without fixing a type.
The coefficient ring here is the natural numbers, not the detector field.
-/

namespace HoffmanChromatic

open scoped BigOperators

noncomputable def weightPolynomial {A : Type*} [Fintype A] (w : A → ℕ) : Polynomial ℕ :=
  ∑ a, Polynomial.X ^ w a

theorem weightPolynomial_pow {A : Type*} [Fintype A] (w : A → ℕ) (n : ℕ) :
    (weightPolynomial w)^n =
      ∑ x : Fin n → A, Polynomial.X ^ (∑ i, w (x i)) := by
  classical
  calc
    (weightPolynomial w)^n = ∏ _i : Fin n, (∑ a : A, (Polynomial.X : Polynomial ℕ)^w a) := by
      simp [weightPolynomial]
    _ = ∑ x : Fin n → A, ∏ i, (Polynomial.X : Polynomial ℕ)^w (x i) := by
      rw [Fintype.prod_sum]
    _ = _ := by simp [Finset.prod_pow_eq_pow_sum]

theorem layer_card_eq_coefficient {A : Type*} [Fintype A] (w : A → ℕ) (n m : ℕ) :
    Fintype.card {x : Fin n → A // ∑ i, w (x i) = m} =
      ((weightPolynomial w)^n).coeff m := by
  classical
  rw [weightPolynomial_pow, Polynomial.finset_sum_coeff, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  rw [Polynomial.coeff_X_pow]
  exact if_congr eq_comm rfl rfl

/-- The sum of surviving coefficient slots equals the weighted coefficient sum. -/
theorem profile_sum_eq_weighted_coefficients {A : Type*} [Fintype A]
    (w : A → ℕ) (n D : ℕ) :
    (∑ x : Fin n → A, (D + 1 - ∑ i, w (x i))) =
      ∑ k ∈ Finset.range (D + 1), (D + 1 - k) * ((weightPolynomial w)^n).coeff k := by
  classical
  rw [weightPolynomial_pow]
  simp_rw [Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow,
    Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (∑ i, w (x i)) < D + 1
  · simp [Finset.mem_range, h]
  · have hz : D + 1 - ∑ i, w (x i) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)
    simp [Finset.mem_range, h, hz]

end HoffmanChromatic
