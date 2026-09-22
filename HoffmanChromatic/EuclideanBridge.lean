import HoffmanChromatic.Geometry
import HoffmanChromatic.RankColoring
import HoffmanChromatic.Targets

/-! The passage from integer-coordinate distance graphs to Euclidean colourings. -/

namespace HoffmanChromatic

open scoped BigOperators

def realPoint {n : ℕ} (x : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 _).symm (fun i => (x i : ℝ))

theorem realPoint_dist_sq {n : ℕ} (x y : Fin n → ℤ) :
    dist (realPoint x) (realPoint y)^2 = (sqDistance x y : ℝ) := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt]
  · simp [realPoint, sqDistance, Real.dist_eq, sq_abs]
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _

noncomputable def scaledPoint {n : ℕ} (P : ℕ) (x : Fin n → ℤ) :
    EuclideanSpace ℝ (Fin n) :=
  (Real.sqrt (2 * (P : ℝ)))⁻¹ • realPoint x

theorem scaledPoint_unit_distance {n : ℕ} (P : ℕ) (hP : 0 < P)
    (x y : Fin n → ℤ) (hxy : sqDistance x y = 2 * (P : ℤ)) :
    dist (scaledPoint P x) (scaledPoint P y) = 1 := by
  have hp : 0 < (2 : ℝ) * P := by positivity
  have hs : 0 < Real.sqrt (2 * (P : ℝ)) := Real.sqrt_pos.2 hp
  have hsq := realPoint_dist_sq x y
  rw [hxy] at hsq
  have hd : dist (realPoint x) (realPoint y) = Real.sqrt (2 * (P : ℝ)) := by
    have hz := dist_nonneg (x := realPoint x) (y := realPoint y)
    have hr := Real.sq_sqrt hp.le
    push_cast at hsq
    nlinarith
  calc
    dist (scaledPoint P x) (scaledPoint P y) =
        (Real.sqrt (2 * (P : ℝ)))⁻¹ * dist (realPoint x) (realPoint y) := by
      simp only [scaledPoint, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hs)]
    _ = 1 := by rw [hd, inv_mul_cancel₀ hs.ne']

theorem finite_detector_obstruction {V K : Type*} [Fintype V] [Field K]
    (n P : ℕ) (hP : 0 < P) (G : SimpleGraph V) (coord : V → Fin n → ℤ)
    (hedge : ∀ x y, G.Adj x y → sqDistance (coord x) (coord y) = 2 * (P : ℤ))
    (M : Matrix V V K) (hdiag : ∀ x, M x x = 1)
    (hoff : ∀ x y, x ≠ y → ¬ G.Adj x y → M x y = 0)
    (k : ℕ) (hcolor : (unitDistanceGraph n).Colorable k) :
    Fintype.card V ≤ k * M.rank := by
  obtain ⟨c⟩ := hcolor
  let cV : G.Coloring (Fin k) := SimpleGraph.Coloring.mk
    (fun x => c (scaledPoint P (coord x))) (by
      intro x y h
      exact c.valid (scaledPoint_unit_distance P hP (coord x) (coord y) (hedge x y h)))
  simpa using card_le_colors_mul_rank G M hdiag hoff cV

end HoffmanChromatic
