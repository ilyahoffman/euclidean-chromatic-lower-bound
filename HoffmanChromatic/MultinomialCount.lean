import HoffmanChromatic.Counting
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Ring

/-! A coefficient contains every type with the prescribed total weight. -/

namespace HoffmanChromatic

open scoped BigOperators

theorem multinomial_le_layer_coefficient {A : Type*} [Fintype A]
    (w k : A → ℕ) :
    Nat.multinomial Finset.univ k ≤
      ((weightPolynomial w)^(∑ i, k i)).coeff (∑ i, w i * k i) := by
  classical
  rw [weightPolynomial, Finset.sum_pow_eq_sum_piAntidiag, Polynomial.finset_sum_coeff]
  have hk : k ∈ Finset.piAntidiag Finset.univ (∑ i, k i) := by
    simp [Finset.mem_piAntidiag]
  have hb := Finset.single_le_sum (s := Finset.piAntidiag Finset.univ (∑ i, k i))
    (f := fun m => ((Nat.multinomial Finset.univ m : Polynomial ℕ) *
      ∏ i, (Polynomial.X^(w i))^(m i)).coeff (∑ i, w i*k i))
    (fun _ _ => Nat.zero_le _) hk
  have hf : (∏ i : A, ((Polynomial.X : Polynomial ℕ)^(w i)) ^ (k i)) =
      Polynomial.X^(∑ i, w i*k i) := by
    simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
  dsimp only at hb
  rw [hf] at hb
  simpa only [← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_self, mul_one] using hb

theorem coefficient_mul_lower (f g : Polynomial ℕ) (a b : ℕ) :
    f.coeff a * g.coeff b ≤ (f*g).coeff (a+b) := by
  rw [Polynomial.coeff_mul]
  exact Finset.single_le_sum (f := fun ij => f.coeff ij.1 * g.coeff ij.2)
    (fun _ _ => Nat.zero_le _)
    (show (a,b) ∈ Finset.antidiagonal (a+b) by simp)

theorem power_linear_coefficient_pos (f : Polynomial ℕ) (hf : 1 ≤ f.coeff 1) (r : ℕ) :
    1 ≤ (f^r).coeff r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ]
    calc
      1 = 1*1 := by rfl
      _ ≤ (f^r).coeff r * f.coeff 1 := Nat.mul_le_mul ih hf
      _ ≤ ((f^r)*f).coeff (r+1) := coefficient_mul_lower (f^r) f r 1

theorem type_with_ones_lower {A : Type*} [Fintype A] (w m : A → ℕ)
    (hlinear : 1 ≤ (weightPolynomial w).coeff 1) (q r : ℕ) :
    Nat.multinomial Finset.univ (fun i => q*m i) ≤
      ((weightPolynomial w)^(q*(∑ i, m i)+r)).coeff (q*(∑ i, w i*m i)+r) := by
  have hn : (∑ i, q*m i) = q*(∑ i, m i) := (Finset.mul_sum ..).symm
  have he : (∑ i, w i*(q*m i)) = q*(∑ i, w i*m i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h := multinomial_le_layer_coefficient w (fun i => q*m i)
  rw [hn, he] at h
  rw [pow_add]
  calc
    _ ≤ ((weightPolynomial w)^(q*(∑ i, m i))).coeff (q*(∑ i, w i*m i)) := h
    _ ≤ ((weightPolynomial w)^(q*(∑ i, m i))).coeff (q*(∑ i, w i*m i)) *
        ((weightPolynomial w)^r).coeff r := by
      exact Nat.le_mul_of_pos_right _ (power_linear_coefficient_pos _ hlinear r)
    _ ≤ _ := coefficient_mul_lower _ _ _ _

end HoffmanChromatic
