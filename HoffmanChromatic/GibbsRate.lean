import HoffmanChromatic.FiniteLaw
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Order.IntermediateValue

/-! Strictly increasing tilted means and attained logarithmic minima. -/
namespace HoffmanChromatic

open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def expMoment (b : J → ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  ∑ j, (b j)^k*Real.exp (b j*y)

theorem expMoment_zero_pos [Nonempty J] (b : J → ℝ) (y : ℝ) : 0<expMoment b 0 y := by
  simp only [expMoment,pow_zero,one_mul]
  exact Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty

theorem expMoment_deriv (b : J → ℝ) (k : ℕ) (y : ℝ) :
    HasDerivAt (expMoment b k) (expMoment b (k+1) y) y := by
  have hh := HasDerivAt.sum (u := Finset.univ) (fun j _ =>
    (((hasDerivAt_id y).const_mul (b j)).exp).const_mul ((b j)^k))
  convert hh using 1
  simp only [expMoment]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_one,pow_succ,id_eq]
  ring

noncomputable def expLaw [Nonempty J] (b : J → ℝ) (y : ℝ) : FiniteLaw J where
  weight := fun j => Real.exp (b j*y)/expMoment b 0 y
  nonneg := fun j => (div_pos (Real.exp_pos _) (expMoment_zero_pos b y)).le
  total := by
    rw [← Finset.sum_div]
    have he : (∑ j, Real.exp (b j*y))=expMoment b 0 y := by simp [expMoment]
    rw [he,div_self (expMoment_zero_pos b y).ne']

noncomputable def expMean (b : J → ℝ) (y : ℝ) : ℝ := expMoment b 1 y/expMoment b 0 y

theorem expLaw_moment [Nonempty J] (b : J → ℝ) (k : ℕ) (y : ℝ) :
    (expLaw b y).mean (fun j => (b j)^k)=expMoment b k y/expMoment b 0 y := by
  simp only [FiniteLaw.mean,expLaw,expMoment,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem finite_variance_identity (p : FiniteLaw J) (f : J → ℝ) :
    p.mean (fun j => (f j-p.mean f)^2)=p.mean (fun j => (f j)^2)-(p.mean f)^2 := by
  have he : (fun j => (f j-p.mean f)^2)=
      (fun j => (f j)^2-2*p.mean f*f j+(p.mean f)^2) := by funext j; ring
  rw [he,FiniteLaw.mean_add,FiniteLaw.mean_sub,FiniteLaw.mean_const_mul,FiniteLaw.mean_const]
  ring

theorem expMean_deriv [Nonempty J] (b : J → ℝ) (y : ℝ) :
    HasDerivAt (expMean b) ((expLaw b y).mean (fun j => (b j-expMean b y)^2)) y := by
  have hm : (expLaw b y).mean b=expMean b y := by
    simpa only [pow_one,expMean] using expLaw_moment b 1 y
  have hv : (expLaw b y).mean (fun j => (b j-expMean b y)^2)=
      expMoment b 2 y/expMoment b 0 y-(expMean b y)^2 := by
    rw [← hm,finite_variance_identity,expLaw_moment,hm]
  rw [hv]
  have hh := (expMoment_deriv b 1 y).div (expMoment_deriv b 0 y) (expMoment_zero_pos b y).ne'
  convert hh using 1
  dsimp [expMean]
  have hz := (expMoment_zero_pos b y).ne'
  field_simp [hz]
  ring

theorem finite_variance_pos_at (p : FiniteLaw J) (f : J → ℝ) (j : J)
    (hp : 0<p.weight j) (hj : f j≠p.mean f) :
    0<p.mean (fun i => (f i-p.mean f)^2) := by
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun i => p.weight i*(f i-p.mean f)^2)
    (fun i _ => mul_nonneg (p.nonneg i) (sq_nonneg _)) (Finset.mem_univ j)
  have hpos : 0<p.weight j*(f j-p.mean f)^2 := mul_pos hp (sq_pos_of_ne_zero (sub_ne_zero.2 hj))
  exact hpos.trans_le hh

theorem expMean_strictMono [Nonempty J] (b : J → ℝ) (i j : J) (hij : b i≠b j) :
    StrictMono (expMean b) := by
  apply strictMono_of_hasDerivAt_pos (expMean_deriv b)
  intro y
  have hm : (expLaw b y).mean b=expMean b y := by
    simpa only [pow_one,expMean] using expLaw_moment b 1 y
  rw [← hm]
  by_cases hi : b i=(expLaw b y).mean b
  · exact finite_variance_pos_at _ _ j
      (div_pos (Real.exp_pos _) (expMoment_zero_pos b y)) (by intro hj; exact hij (hi.trans hj.symm))
  · exact finite_variance_pos_at _ _ i
      (div_pos (Real.exp_pos _) (expMoment_zero_pos b y)) hi

theorem expMean_monotone [Nonempty J] (b : J → ℝ) : Monotone (expMean b) := by
  apply monotone_of_hasDerivAt_nonneg (expMean_deriv b)
  intro y
  exact (expLaw b y).mean_nonneg fun j => sq_nonneg _

noncomputable def expLog [Nonempty J] (b : J → ℝ) (y : ℝ) : ℝ :=
  Real.log (expMoment b 0 y)

theorem expLog_deriv [Nonempty J] (b : J → ℝ) (y : ℝ) :
    HasDerivAt (expLog b) (expMean b y) y := by
  exact (expMoment_deriv b 0 y).log (expMoment_zero_pos b y).ne'

/-- The supporting line to log Z(exp y), proved on the whole real line. -/
theorem expLog_tangent [Nonempty J] (b : J → ℝ) (y z : ℝ) :
    expLog b y+expMean b y*(z-y)≤expLog b z := by
  have hd : Differentiable ℝ (expLog b) := fun y => (expLog_deriv b y).differentiableAt
  have hm := expMean_monotone b
  rcases lt_trichotomy y z with hyz | heq | hzy
  · obtain ⟨w,hw,hs⟩ := exists_deriv_eq_slope (expLog b) hyz hd.continuous.continuousOn hd.differentiableOn
    rw [(expLog_deriv b w).deriv] at hs
    have hle := hm hw.1.le
    rw [hs] at hle
    have hh := (le_div_iff₀ (sub_pos.2 hyz)).mp hle
    linarith only [hh]
  · subst z
    simp
  · obtain ⟨w,hw,hs⟩ := exists_deriv_eq_slope (expLog b) hzy hd.continuous.continuousOn hd.differentiableOn
    rw [(expLog_deriv b w).deriv] at hs
    have hle := hm hw.2.le
    rw [hs] at hle
    have hh := (div_le_iff₀ (sub_pos.2 hzy)).mp hle
    nlinarith only [hh]

theorem expLog_minimum [Nonempty J] (b : J → ℝ) (y m : ℝ) (hm : expMean b y=m) (z : ℝ) :
    expLog b y-m*y≤expLog b z-m*z := by
  have hh := expLog_tangent b y z
  rw [hm] at hh
  nlinarith only [hh]

theorem expMean_exists_unique [Nonempty J] (b : J → ℝ) (i j : J) (hij : b i≠b j)
    (l u m : ℝ) (hlu : l<u) (hl : expMean b l<m) (hu : m<expMean b u) :
    ∃ y : ℝ, l<y ∧ y<u ∧ expMean b y=m ∧ ∀ z : ℝ, expMean b z=m → z=y := by
  have hcont : Continuous (expMean b) := continuous_iff_continuousAt.2 fun y =>
    (expMean_deriv b y).continuousAt
  obtain ⟨y,hy,hm⟩ := intermediate_value_Ioo hlu.le hcont.continuousOn (show m∈Set.Ioo (expMean b l) (expMean b u) from ⟨hl,hu⟩)
  refine ⟨y,hy.1,hy.2,hm,?_⟩
  intro z hz
  exact (expMean_strictMono b i j hij).injective (hz.trans hm.symm)

end HoffmanChromatic
