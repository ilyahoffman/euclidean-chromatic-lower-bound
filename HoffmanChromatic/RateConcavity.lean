import HoffmanChromatic.SaddlePoint
import Mathlib.Analysis.Convex.Continuous

/-! Order properties of the infimum, with its boundedness proved explicitly. -/
namespace HoffmanChromatic

open scoped BigOperators

variable {A : Type*} [Fintype A]

theorem partition01_ge_one (b : A → ℕ) (x : ℝ) (hx : 0≤x) : 1≤partition01 b x := by
  have hs : 0≤∑ j, x^(b j) := Finset.sum_nonneg fun _ _ => pow_nonneg hx _
  dsimp [partition01]
  linarith

theorem rate_expression_nonneg (b : A → ℕ) (m x : ℝ) (hm : 0≤m) (hx : 0<x) (hx1 : x<1) :
    0≤Real.log (partition01 b x)-m*Real.log x := by
  have hZ := Real.log_nonneg (partition01_ge_one b x hx.le)
  have hlog := Real.log_nonpos hx.le hx1.le
  have hp := mul_nonpos_of_nonneg_of_nonpos hm hlog
  linarith

theorem logarithmicRate01_bddBelow (b : A → ℕ) (m : ℝ) (hm : 0≤m) :
    BddBelow {v : ℝ | ∃ x : ℝ, 0<x ∧ x<1 ∧ v=Real.log (partition01 b x)-m*Real.log x} := by
  refine ⟨0,?_⟩
  intro v hv
  obtain ⟨x,hx,hx1,rfl⟩ := hv
  exact rate_expression_nonneg b m x hm hx hx1

theorem logarithmicRate01_nonempty (b : A → ℕ) (m : ℝ) :
    Set.Nonempty {v : ℝ | ∃ x : ℝ, 0<x ∧ x<1 ∧ v=Real.log (partition01 b x)-m*Real.log x} := by
  exact ⟨_,(1/2:ℝ),by norm_num,by norm_num,rfl⟩

theorem logarithmicRate01_le (b : A → ℕ) (m x : ℝ) (hm : 0≤m) (hx : 0<x) (hx1 : x<1) :
    logarithmicRate (partition01 b) m≤Real.log (partition01 b x)-m*Real.log x := by
  exact csInf_le (logarithmicRate01_bddBelow b m hm) ⟨x,hx,hx1,rfl⟩

theorem logarithmicRate01_nonneg (b : A → ℕ) (m : ℝ) (hm : 0≤m) :
    0≤logarithmicRate (partition01 b) m := by
  apply le_csInf (logarithmicRate01_nonempty b m)
  intro v hv
  obtain ⟨x,hx,hx1,rfl⟩ := hv
  exact rate_expression_nonneg b m x hm hx hx1

theorem logarithmicRate01_concave (b : A → ℕ) :
    ConcaveOn ℝ (Set.Ici 0) (logarithmicRate (partition01 b)) := by
  refine ⟨convex_Ici 0,?_⟩
  intro m hm k hk a d ha hd had
  change a*logarithmicRate (partition01 b) m+d*logarithmicRate (partition01 b) k≤
    logarithmicRate (partition01 b) (a*m+d*k)
  apply le_csInf (logarithmicRate01_nonempty b (a*m+d*k))
  intro v hv
  obtain ⟨x,hx,hx1,rfl⟩ := hv
  have h1 := mul_le_mul_of_nonneg_left (logarithmicRate01_le b m x hm hx hx1) ha
  have h2 := mul_le_mul_of_nonneg_left (logarithmicRate01_le b k x hk hx hx1) hd
  have he : a*(Real.log (partition01 b x)-m*Real.log x)+
      d*(Real.log (partition01 b x)-k*Real.log x)=
      Real.log (partition01 b x)-(a*m+d*k)*Real.log x := by
    nlinarith only [congrArg (fun z : ℝ => z*Real.log (partition01 b x)) had]
  rw [← he]
  exact add_le_add h1 h2

theorem logarithmicRate01_continuous (b : A → ℕ) :
    ContinuousOn (logarithmicRate (partition01 b)) (Set.Ioi 0) := by
  simpa using (logarithmicRate01_concave b).continuousOn_interior

end HoffmanChromatic
