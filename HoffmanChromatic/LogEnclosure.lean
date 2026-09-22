import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Rational logarithm enclosures with a kernel-checked remainder bound. -/
namespace HoffmanChromatic

open scoped BigOperators

noncomputable def logEta (x : ℝ) : ℝ := (x-1)/(x+1)
noncomputable def logTaylorSum (y : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, y^(j+1)/((j:ℝ)+1)
noncomputable def logApprox (x : ℝ) (N : ℕ) : ℝ :=
  logTaylorSum (logEta x) N-logTaylorSum (-logEta x) N
noncomputable def logError (x : ℝ) (N : ℕ) : ℝ :=
  2*|logEta x|^(N+1)/(1-|logEta x|)

theorem logEta_abs_lt_one (x : ℝ) (hx : 0<x) : |logEta x|<1 := by
  have hx1 : 0<x+1 := by positivity
  rw [abs_lt]
  constructor
  · unfold logEta
    apply (lt_div_iff₀ hx1).2
    linarith
  · unfold logEta
    apply (div_lt_iff₀ hx1).2
    linarith

/-- A slightly looser remainder than the article's atanh bound suffices for
all finite enclosures.  This theorem uses only exact real identities. -/
theorem log_rational_enclosure (x : ℝ) (hx : 0<x) (N : ℕ) :
    logApprox x N-logError x N≤Real.log x ∧ Real.log x≤logApprox x N+logError x N := by
  have hη := logEta_abs_lt_one x hx
  have hη' : |-logEta x|<1 := by simpa using hη
  have hp := Real.abs_log_sub_add_sum_range_le hη' N
  have hm := Real.abs_log_sub_add_sum_range_le hη N
  simp only [abs_neg,sub_neg_eq_add] at hp
  change |logTaylorSum (-logEta x) N+Real.log (1+logEta x)|≤
    |logEta x|^(N+1)/(1-|logEta x|) at hp
  change |logTaylorSum (logEta x) N+Real.log (1-logEta x)|≤
    |logEta x|^(N+1)/(1-|logEta x|) at hm
  have hηp : 0<1+logEta x := by have := (abs_lt.mp hη).1; linarith
  have hηm : 0<1-logEta x := by have := (abs_lt.mp hη).2; linarith
  have hdiv : (1+logEta x)/(1-logEta x)=x := by
    have hx1 : x+1≠0 := by positivity
    apply (div_eq_iff hηm.ne').2
    unfold logEta
    field_simp
    ring
  have hlog : Real.log (1+logEta x)-Real.log (1-logEta x)=Real.log x := by
    rw [← Real.log_div hηp.ne' hηm.ne',hdiv]
  have hp' := abs_le.mp hp
  have hm' := abs_le.mp hm
  have herr : logError x N=2*(|logEta x|^(N+1)/(1-|logEta x|)) := by dsimp [logError]; ring
  rw [herr]
  dsimp [logApprox]
  constructor <;> linarith only [hp'.1,hp'.2,hm'.1,hm'.2,hlog]

theorem log_between_of_series (x l u L U : ℝ) (N M : ℕ) (hl : 0<l)
    (hlx : l≤x) (hxu : x≤u)
    (hL : L≤logApprox l N-logError l N) (hU : logApprox u M+logError u M≤U) :
    L≤Real.log x ∧ Real.log x≤U := by
  have hx : 0<x := hl.trans_le hlx
  have hu : 0<u := hx.trans_le hxu
  exact ⟨hL.trans ((log_rational_enclosure l hl N).1.trans (Real.log_le_log hl hlx)),
    (Real.log_le_log hx hxu).trans ((log_rational_enclosure u hu M).2.trans hU)⟩

end HoffmanChromatic
