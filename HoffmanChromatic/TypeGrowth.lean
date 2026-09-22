import HoffmanChromatic.MultinomialRate

/-! Exponential margins absorb the polynomial losses in a fixed type. -/

namespace HoffmanChromatic

open scoped BigOperators Topology
open Filter

theorem affine_nat_div_rate (K r : ℕ) :
    Tendsto (fun q : ℕ => ((q*K+r:ℕ):ℝ)/(q:ℝ)) atTop (𝓝 (K:ℝ)) := by
  have h := (constant_div_nat_tendsto_zero (r:ℝ)).const_add (K:ℝ)
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  push_cast
  field_simp
  ring

theorem log_affine_nat_div_zero (K r : ℕ) :
    Tendsto (fun q : ℕ => Real.log ((q*K+r+1:ℕ):ℝ)/(q:ℝ)) atTop (𝓝 0) := by
  have h := log_nat_div_nat_tendsto_zero.add
    (constant_div_nat_tendsto_zero (Real.log ((K+r+1:ℕ):ℝ)))
  rw [zero_add] at h
  apply squeeze_zero' ?_ ?_ h
  · filter_upwards [] with q
    apply div_nonneg _ (Nat.cast_nonneg q)
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ q*K+r+1 by omega)
  · filter_upwards [eventually_ge_atTop 1] with q hq
    have hqR : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hcR : (0:ℝ) < ((K+r+1:ℕ):ℝ) := by positivity
    have haR : (0:ℝ) < ((q*K+r+1:ℕ):ℝ) := by positivity
    have hb : ((q*K+r+1:ℕ):ℝ) ≤ (q:ℝ)*((K+r+1:ℕ):ℝ) := by
      have hqr : (1:ℝ) ≤ q := by exact_mod_cast hq
      have hr : (0:ℝ) ≤ r := Nat.cast_nonneg _
      push_cast
      nlinarith
    have hl := Real.log_le_log haR hb
    rw [Real.log_mul hqR.ne' hcR.ne'] at hl
    rw [← add_div]
    exact div_le_div_of_nonneg_right hl hqR.le

theorem fixed_type_exponential_margin {A : Type*} [Fintype A]
    (m : A → ℕ) (K r : ℕ) (t D b : ℝ) (ht : 0 < t) (hD : 0 < D) (hb : 0 < b)
    (hmargin : 0 < typeEntropy m + (K:ℝ)*Real.log t - (∑ i, (m i:ℝ))*Real.log D) :
    ∀ᶠ q : ℕ in atTop,
      b * ((q*K+r+1:ℕ):ℝ) * D^(q*(∑ i, m i)+r) <
        (Nat.multinomial Finset.univ (fun i => q*m i):ℝ) * t^(q*K+r) := by
  let M := ∑ i, m i
  let R (q : ℕ) : ℝ := (Nat.multinomial Finset.univ (fun i => q*m i):ℝ)*t^(q*K+r)
  let L (q : ℕ) : ℝ := b*((q*K+r+1:ℕ):ℝ)*D^(q*M+r)
  have hR : ∀ q, 0 < R q := by
    intro q
    apply mul_pos _ (pow_pos ht _)
    exact_mod_cast Nat.multinomial_pos Finset.univ (fun i => q*m i)
  have hL : ∀ q, 0 < L q := by intro q; dsimp [L]; positivity
  have h : Tendsto (fun q => Real.log (R q)/(q:ℝ) - Real.log (L q)/(q:ℝ)) atTop
      (𝓝 (typeEntropy m + (K:ℝ)*Real.log t - (∑ i, (m i:ℝ))*Real.log D)) := by
    have h' := (((multinomial_log_rate m).add ((affine_nat_div_rate K r).mul_const (Real.log t))).sub
      (constant_div_nat_tendsto_zero (Real.log b))).sub (log_affine_nat_div_zero K r)
    have h'' := h'.sub ((affine_nat_div_rate M r).mul_const (Real.log D))
    simp only [sub_zero, M, Nat.cast_sum] at h''
    apply h''.congr'
    filter_upwards [] with q
    have hp : (0:ℝ) < Nat.multinomial Finset.univ (fun i => q*m i) := by
      exact_mod_cast Nat.multinomial_pos Finset.univ (fun i => q*m i)
    dsimp [R, L]
    rw [Real.log_mul hp.ne' (pow_ne_zero _ ht.ne'), Real.log_pow,
      Real.log_mul (by positivity) (pow_ne_zero _ hD.ne'), Real.log_pow,
      Real.log_mul hb.ne' (by positivity)]
    ring
  have he : ∀ᶠ q : ℕ in atTop, 0 < Real.log (R q)/(q:ℝ) - Real.log (L q)/(q:ℝ) :=
    h.eventually (isOpen_Ioi.mem_nhds hmargin)
  filter_upwards [he, eventually_ge_atTop 1] with q hq hq1
  have hqR : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  apply (Real.log_lt_log_iff (hL q) (hR q)).mp
  exact (div_lt_div_iff_of_pos_right hqR).mp (sub_pos.mp hq)

end HoffmanChromatic
