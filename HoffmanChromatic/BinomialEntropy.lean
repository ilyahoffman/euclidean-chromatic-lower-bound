import HoffmanChromatic.StirlingBounds
import Mathlib.Data.Nat.Choose.Basic

/-! Quantitative binomial ingredients for the remaining local coefficient estimate. -/
namespace HoffmanChromatic

noncomputable def bernoulliDivergence (u t : ℝ) : ℝ :=
  u*Real.log (u/t)+(1-u)*Real.log ((1-u)/(1-t))

theorem bernoulliDivergence_nonneg (u t : ℝ) (hu : 0<u) (hu1 : u<1) (ht : 0<t) (ht1 : t<1) :
    0 ≤ bernoulliDivergence u t := by
  have hc : 0<1-u := by linarith
  have hd : 0<1-t := by linarith
  have ha := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ht hu)) hu.le
  have hb := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hd hc)) hc.le
  rw [Real.log_div ht.ne' hu.ne'] at ha
  rw [Real.log_div hd.ne' hc.ne'] at hb
  have hai : u*(t/u-1)=t-u := by field_simp
  have hbi : (1-u)*((1-t)/(1-u)-1)=u-t := by field_simp
  rw [hai] at ha
  rw [hbi] at hb
  unfold bernoulliDivergence
  rw [Real.log_div hu.ne' ht.ne', Real.log_div hc.ne' hd.ne']
  linarith

theorem bernoulliDivergence_upper (u t : ℝ) (hu : 0<u) (hu1 : u<1) (ht : 0<t) (ht1 : t<1) :
    bernoulliDivergence u t ≤ (u-t)^2/(t*(1-t)) := by
  have hc : 0<1-u := by linarith
  have hd : 0<1-t := by linarith
  have ha := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hu ht)) hu.le
  have hb := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hc hd)) hc.le
  have he : u*(u/t-1)+(1-u)*((1-u)/(1-t)-1) = (u-t)^2/(t*(1-t)) := by
    field_simp
    ring
  exact (add_le_add ha hb).trans_eq he

noncomputable def binomialMass (n k : ℕ) (t : ℝ) : ℝ :=
  (n.choose k:ℝ)*t^k*(1-t)^(n-k)

theorem binomialMass_pos {n k : ℕ} (hkn : k ≤ n) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    0 < binomialMass n k t := by
  have hc : (0:ℝ)<n.choose k := by exact_mod_cast Nat.choose_pos hkn
  unfold binomialMass
  exact mul_pos (mul_pos hc (pow_pos ht _)) (pow_pos (by linarith) _)

theorem log_binomialMass {n k : ℕ} (hkn : k ≤ n) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    Real.log (binomialMass n k t) = Real.log (n.factorial:ℝ)-Real.log (k.factorial:ℝ)-
      Real.log ((n-k).factorial:ℝ)+(k:ℝ)*Real.log t+((n-k:ℕ):ℝ)*Real.log (1-t) := by
  have hc : (0:ℝ)<n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hk : (0:ℝ)<k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hl : (0:ℝ)<(n-k).factorial := by exact_mod_cast Nat.factorial_pos (n-k)
  have hh := congrArg (fun a : ℕ => Real.log (a:ℝ)) (Nat.choose_mul_factorial_mul_factorial hkn)
  push_cast at hh
  rw [Real.log_mul (mul_ne_zero hc.ne' hk.ne') hl.ne', Real.log_mul hc.ne' hk.ne'] at hh
  unfold binomialMass
  rw [Real.log_mul (mul_ne_zero hc.ne' (pow_ne_zero _ ht.ne')) (pow_ne_zero _ (by linarith)),
    Real.log_mul hc.ne' (pow_ne_zero _ ht.ne'), Real.log_pow, Real.log_pow]
  linarith

/-- The logarithmic local estimate with the full inverse-square-root term. -/
theorem binomial_stirling_identity {n k : ℕ} (hk : 0<k) (hkn : k<n)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    let u := (k:ℝ)/(n:ℝ)
    Real.log (binomialMass n k t)+(n:ℝ)*bernoulliDivergence u t+
      (1/2:ℝ)*Real.log ((n:ℝ)*u*(1-u)) =
      logFactorialError n-logFactorialError k-logFactorialError (n-k) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (lt_trans hk hkn)
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hknR : (k:ℝ)<n := by exact_mod_cast hkn
  have hlR : (0:ℝ)<(n:ℝ)-k := by linarith
  have hnc : ((n-k:ℕ):ℝ)=(n:ℝ)-k := Nat.cast_sub hkn.le
  have hu : 0<(k:ℝ)/(n:ℝ) := div_pos hkR hnR
  have hv : 0<1-(k:ℝ)/(n:ℝ) := by rw [sub_pos, div_lt_one hnR]; exact hknR
  have hi : 1-(k:ℝ)/(n:ℝ)=((n:ℝ)-k)/(n:ℝ) := by field_simp
  dsimp only
  rw [log_binomialMass hkn.le ht ht1]
  unfold bernoulliDivergence logFactorialError
  rw [Real.log_mul (mul_ne_zero hnR.ne' hu.ne') hv.ne',
    Real.log_mul hnR.ne' hu.ne', Real.log_div hu.ne' ht.ne',
    Real.log_div hv.ne' (by linarith : (1-t)≠0), hi,
    Real.log_div hkR.ne' hnR.ne', Real.log_div hlR.ne' hnR.ne', hnc]
  field_simp
  ring

theorem binomial_log_error_bounded : ∃ C : ℝ, 0≤C ∧ ∀ n k : ℕ, 0<k → k<n →
    ∀ t : ℝ, 0<t → t<1 →
    let u := (k:ℝ)/(n:ℝ)
    |Real.log (binomialMass n k t)+(n:ℝ)*bernoulliDivergence u t+
      (1/2:ℝ)*Real.log ((n:ℝ)*u*(1-u))| ≤ C := by
  obtain ⟨C, hC, hb⟩ := log_factorial_error_bounded
  refine ⟨3*C, by positivity, ?_⟩
  intro n k hk hkn t ht ht1
  dsimp only
  rw [binomial_stirling_identity hk hkn ht ht1]
  have hn := hb n (lt_trans hk hkn)
  have hh := hb k hk
  have hl := hb (n-k) (Nat.sub_pos_of_lt hkn)
  change |logFactorialError n|≤C at hn
  change |logFactorialError k|≤C at hh
  change |logFactorialError (n-k)|≤C at hl
  calc
    _ ≤ |logFactorialError n|+|logFactorialError k|+|logFactorialError (n-k)| :=
      (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
    _ ≤ 3*C := by linarith

end HoffmanChromatic
