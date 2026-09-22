import HoffmanChromatic.GibbsRate
import HoffmanChromatic.TiltedPolynomial

/-! Unique saddle parameters and identification of the actual infimum. -/
namespace HoffmanChromatic

open scoped BigOperators

variable {A : Type*} [Fintype A]

def fullWeights01 (b : A → ℕ) : Option (Option A) → ℝ
  | none => 0
  | some none => 1
  | some (some j) => b j

theorem expMoment01_zero (b : A → ℕ) (x : ℝ) (hx : 0<x) :
    expMoment (fullWeights01 b) 0 (Real.log x)=partition01 b x := by
  simp [expMoment,fullWeights01,Fintype.sum_option,Real.exp_nat_mul,Real.exp_log hx,partition01,add_assoc]

theorem expMean01 (b : A → ℕ) (x : ℝ) (hx : 0<x) :
    expMean (fullWeights01 b) (Real.log x)=mean01 b x := by
  rw [expMean,expMoment01_zero b x hx]
  simp [expMoment,fullWeights01,Fintype.sum_option,Real.exp_nat_mul,Real.exp_log hx,mean01]

theorem expLog01 (b : A → ℕ) (x : ℝ) (hx : 0<x) :
    expLog (fullWeights01 b) (Real.log x)=Real.log (partition01 b x) := by
  rw [expLog,expMoment01_zero b x hx]

theorem mean01_strictMonoOn (b : A → ℕ) : StrictMonoOn (mean01 b) (Set.Ioi 0) := by
  intro x hx y hy hxy
  rw [← expMean01 b x hx,← expMean01 b y hy]
  exact expMean_strictMono (fullWeights01 b) none (some none) (by norm_num [fullWeights01])
    (Real.log_lt_log hx hxy)

theorem saddle_exists_unique (b : A → ℕ) (l u m : ℝ) (hl : 0<l) (hlu : l<u)
    (hml : mean01 b l<m) (hmu : m<mean01 b u) :
    ∃ x : ℝ, l<x ∧ x<u ∧ mean01 b x=m ∧ ∀ z : ℝ, 0<z → mean01 b z=m → z=x := by
  have hu : 0<u := hl.trans hlu
  have hb : fullWeights01 b none≠fullWeights01 b (some none) := by norm_num [fullWeights01]
  obtain ⟨y,hyL,hyU,hm,hyuniq⟩ := expMean_exists_unique (fullWeights01 b) none (some none) hb
    (Real.log l) (Real.log u) m (Real.log_lt_log hl hlu)
    (by rwa [expMean01 b l hl]) (by rwa [expMean01 b u hu])
  refine ⟨Real.exp y,?_,?_,?_,?_⟩
  · have hh := Real.exp_lt_exp.mpr hyL
    rwa [Real.exp_log hl] at hh
  · have hh := Real.exp_lt_exp.mpr hyU
    rwa [Real.exp_log hu] at hh
  · rw [← expMean01 b (Real.exp y) (Real.exp_pos _),Real.log_exp]
    exact hm
  · intro z hz hzm
    have hh := hyuniq (Real.log z) (by rwa [expMean01 b z hz])
    have he := congrArg Real.exp hh
    rwa [Real.exp_log hz] at he

theorem logarithmicRate_at_saddle (b : A → ℕ) (x m : ℝ) (hx : 0<x) (hx1 : x<1)
    (hm : mean01 b x=m) :
    logarithmicRate (partition01 b) m=Real.log (partition01 b x)-m*Real.log x := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨x,hx,hx1,rfl⟩
  · intro v hv
    obtain ⟨y,hy,hy1,rfl⟩ := hv
    have hh := expLog_minimum (fullWeights01 b) (Real.log x) m
      (by rwa [expMean01 b x hx]) (Real.log y)
    simpa only [expLog01 b x hx,expLog01 b y hy] using hh

theorem partition_log_tangent (b : A → ℕ) (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    Real.log (partition01 b x)+mean01 b x*(Real.log y-Real.log x)≤Real.log (partition01 b y) := by
  have hh := expLog_tangent (fullWeights01 b) (Real.log x) (Real.log y)
  simpa only [expLog01 b x hx,expLog01 b y hy,expMean01 b x hx] using hh

end HoffmanChromatic
