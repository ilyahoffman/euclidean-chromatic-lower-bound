import HoffmanChromatic.MultinomialCount
import HoffmanChromatic.StirlingBounds

/-! The logarithmic growth rate of every fixed multinomial type. -/

namespace HoffmanChromatic

open scoped BigOperators Topology
open Filter

theorem log_multinomial {A : Type*} [Fintype A] (m : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ m : ℝ) =
      Real.log ((∑ i, m i).factorial : ℝ) - ∑ i, Real.log ((m i).factorial : ℝ) := by
  have hm : (0:ℝ) < Nat.multinomial Finset.univ m := by
    exact_mod_cast Nat.multinomial_pos Finset.univ m
  have hp : (0:ℝ) < ∏ i : A, ((m i).factorial : ℝ) := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast Nat.factorial_pos (m i)
  have he := congrArg (fun a : ℕ => Real.log (a : ℝ)) (Nat.multinomial_spec Finset.univ m)
  push_cast at he
  rw [Real.log_mul hp.ne' hm.ne', Real.log_prod] at he
  · linarith
  · intro i _
    exact_mod_cast (Nat.factorial_ne_zero (m i))

noncomputable def typeEntropy {A : Type*} [Fintype A] (m : A → ℕ) : ℝ :=
  (∑ i, (m i:ℝ)) * Real.log (∑ i, (m i:ℝ)) - ∑ i, (m i:ℝ)*Real.log (m i:ℝ)

theorem multinomial_log_rate {A : Type*} [Fintype A] (m : A → ℕ) :
    Tendsto (fun q : ℕ => Real.log (Nat.multinomial Finset.univ (fun i => q*m i) : ℝ)/(q:ℝ))
      atTop (𝓝 (typeEntropy m)) := by
  have hs := tendsto_finset_sum Finset.univ (fun i _ => log_factorial_multiple_rate (m i))
  have h := (log_factorial_multiple_rate (∑ i, m i)).sub hs
  convert h using 1
  · funext q
    rw [log_multinomial, ← Finset.mul_sum]
    simp only [sub_div, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul, Nat.cast_sum]
    ring
  · unfold typeEntropy
    simp only [Finset.sum_sub_distrib, Nat.cast_sum]
    ring_nf

theorem gibbs_type_entropy {A : Type*} [Fintype A] [Nonempty A]
    (w m : A → ℕ) (t L : ℝ) (ht : 0 < t) (hL : 0 < L)
    (hm : ∀ i, (m i : ℝ) = L*t^(w i)) :
    typeEntropy m = (∑ i, (m i:ℝ))*Real.log (∑ i, t^(w i)) -
      (∑ i, (m i:ℝ)*(w i:ℝ))*Real.log t := by
  classical
  have hZ : 0 < ∑ i : A, t^(w i) := Finset.sum_pos
    (fun i _ => pow_pos ht _) Finset.univ_nonempty
  have hsum : (∑ i, (m i:ℝ)) = L*(∑ i, t^(w i)) := by simp_rw [hm]; rw [Finset.mul_sum]
  have hi : ∀ i, Real.log (m i:ℝ) = Real.log L + (w i:ℝ)*Real.log t := by
    intro i
    rw [hm, Real.log_mul hL.ne' (pow_ne_zero _ ht.ne'), Real.log_pow]
  have hlogsum : Real.log (∑ i, (m i:ℝ)) = Real.log L + Real.log (∑ i, t^(w i)) := by
    rw [hsum, Real.log_mul hL.ne' hZ.ne']
  have hsumlog : (∑ i, (m i:ℝ)*Real.log (m i:ℝ)) =
      (∑ i, (m i:ℝ))*Real.log L + (∑ i, (m i:ℝ)*(w i:ℝ))*Real.log t := by
    simp_rw [hi, mul_add, ← mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  unfold typeEntropy
  rw [hlogsum, hsumlog]
  ring

end HoffmanChromatic
