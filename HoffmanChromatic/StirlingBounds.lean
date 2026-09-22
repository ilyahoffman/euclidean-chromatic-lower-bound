import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Uniform logarithmic factorial estimates from mathlib's proved Stirling bounds. -/

namespace HoffmanChromatic

open scoped BigOperators Nat Topology
open Real
open Filter

theorem log_factorial_error_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
    |Real.log (n.factorial : ℝ) - (((n : ℝ) + 1/2) * Real.log (n : ℝ) - n)| ≤ C := by
  obtain ⟨a, ha, hbound⟩ := Stirling.stirlingSeq'_bounded_by_pos_constant
  let b := Stirling.stirlingSeq 1
  have hb : 0 < b := Stirling.stirlingSeq'_pos 0
  refine ⟨max |Real.log a + (1/2)*Real.log 2| |Real.log b + (1/2)*Real.log 2|,
    le_trans (abs_nonneg _) (le_max_left _ _), ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hl := hbound m
  have hu : Stirling.stirlingSeq (m+1) ≤ b :=
    Stirling.stirlingSeq'_antitone (show 0 ≤ m from Nat.zero_le _)
  have hp := Stirling.stirlingSeq'_pos m
  have hlo := Real.log_le_log ha hl
  have hup := Real.log_le_log hp hu
  have hnreal : (0:ℝ) < (m+1:ℕ) := by positivity
  have hformula := Stirling.log_stirlingSeq_formula (m+1)
  rw [Real.log_mul (by norm_num) (ne_of_gt hnreal),
    Real.log_div (ne_of_gt hnreal) (ne_of_gt (Real.exp_pos 1)), Real.log_exp] at hformula
  apply abs_le.mpr
  constructor
  · have h := neg_abs_le (Real.log a + (1/2)*Real.log 2)
    have hm := le_max_left |Real.log a + (1/2)*Real.log 2| |Real.log b + (1/2)*Real.log 2|
    nlinarith
  · have h := le_abs_self (Real.log b + (1/2)*Real.log 2)
    have hm := le_max_right |Real.log a + (1/2)*Real.log 2| |Real.log b + (1/2)*Real.log 2|
    nlinarith

theorem log_nat_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
  simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

theorem constant_div_nat_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))

noncomputable def logFactorialError (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) - (((n : ℝ)+1/2)*Real.log (n : ℝ)-n)

/-- Factorial growth along every fixed integer type multiplicity. -/
theorem log_factorial_multiple_rate (a : ℕ) :
    Tendsto (fun n : ℕ => Real.log ((n*a).factorial : ℝ)/(n:ℝ) - (a:ℝ)*Real.log (n:ℝ))
      atTop (𝓝 ((a:ℝ)*Real.log (a:ℝ)-a)) := by
  by_cases ha : a = 0
  · subst a
    simp
  have haR : (0:ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
  obtain ⟨C, hC, herr⟩ := log_factorial_error_bounded
  have herr0 : Tendsto (fun n : ℕ => logFactorialError (n*a)/(n:ℝ)) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (g := fun n : ℕ => C/(n:ℝ)) ?_ (constant_div_nat_tendsto_zero C)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [abs_div, abs_of_pos hnR]
    exact div_le_div_of_nonneg_right (herr (n*a) (Nat.mul_pos (by omega) (Nat.pos_of_ne_zero ha))) hnR.le
  have hlog : Tendsto (fun n : ℕ => Real.log ((n*a:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    have h := log_nat_div_nat_tendsto_zero.add (constant_div_nat_tendsto_zero (Real.log (a:ℝ)))
    rw [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    simp only [Nat.cast_mul, Real.log_mul hnR.ne' haR.ne', add_div]
  have hh : Tendsto (fun n : ℕ => ((a:ℝ)*Real.log (a:ℝ)-(a:ℝ)) +
      (1/2)*(Real.log ((n*a:ℕ):ℝ)/(n:ℝ)) + logFactorialError (n*a)/(n:ℝ))
      atTop (𝓝 ((a:ℝ)*Real.log (a:ℝ)-(a:ℝ))) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add (hlog.const_mul (1/2))).add herr0
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold logFactorialError
  rw [Nat.cast_mul, Real.log_mul hnR.ne' haR.ne']
  field_simp
  ring

end HoffmanChromatic
