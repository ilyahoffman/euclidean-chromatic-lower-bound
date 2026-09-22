import HoffmanChromatic.Alphabets
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Elementary coefficient upper bounds used by the asymptotic arguments. -/

namespace HoffmanChromatic

open scoped BigOperators

noncomputable def natEval (f : Polynomial ℕ) (x : ℝ) : ℝ :=
  f.eval₂ (Nat.castRingHom ℝ) x

theorem natEval_sum (f : Polynomial ℕ) (x : ℝ) :
    natEval f x = ∑ k ∈ f.support, (f.coeff k : ℝ)*x^k := by
  rw [natEval, Polynomial.eval₂_eq_sum]
  rfl

theorem partial_coefficient_sum_le (f : Polynomial ℕ) (x : ℝ) (hx : 0 ≤ x) (s : Finset ℕ) :
    (∑ k ∈ s, (f.coeff k : ℝ)*x^k) ≤ natEval f x := by
  classical
  rw [natEval_sum]
  calc
    _ ≤ ∑ k ∈ s ∪ f.support, (f.coeff k : ℝ)*x^k :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun k _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _))
    _ = _ := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro k _ hk
      have h := Polynomial.not_mem_support_iff.mp hk
      simp [h]

theorem coefficient_eval_le (f : Polynomial ℕ) (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (f.coeff k : ℝ)*x^k ≤ natEval f x := by
  simpa using partial_coefficient_sum_le f x hx {k}

theorem weightedCount_eval_bound (E : Polynomial ℕ) (n D : ℕ)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    (weightedCount E n D : ℝ) * s^D ≤ ((D:ℝ)+1) * (natEval E s)^n := by
  classical
  rw [weightedCount]
  push_cast
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ k ∈ Finset.range (D+1), ((D:ℝ)+1) * ((E^n).coeff k : ℝ) * s^k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkD : k ≤ D := by have := Finset.mem_range.mp hk; omega
      have hw : ((D+1-k:ℕ):ℝ) ≤ (D:ℝ)+1 := by exact_mod_cast Nat.sub_le (D+1) k
      have hp : s^D ≤ s^k := pow_le_pow_of_le_one hs.le hs1 hkD
      calc
        _ ≤ ((D:ℝ)+1) * ((E^n).coeff k : ℝ) * s^D := by
          gcongr
        _ ≤ ((D:ℝ)+1) * ((E^n).coeff k : ℝ) * s^k := by
          exact mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((D:ℝ)+1) * ∑ k ∈ Finset.range (D+1), ((E^n).coeff k : ℝ) * s^k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ ((D:ℝ)+1) * natEval (E^n) s :=
      mul_le_mul_of_nonneg_left (partial_coefficient_sum_le (E^n) s hs.le _) (by positivity)
    _ = _ := by simp [natEval, Polynomial.eval₂_pow]

end HoffmanChromatic
