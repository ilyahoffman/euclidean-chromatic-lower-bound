import HoffmanChromatic.Targets
import Mathlib.Tactic.Linarith

/-! Euclidean dimension monotonicity and the power-of-two cover. -/
namespace HoffmanChromatic

open scoped BigOperators

noncomputable def zeroExtend (n m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n+m)) :=
  (WithLp.equiv 2 _).symm (Fin.addCases (fun i => x i) (fun _ => 0))

theorem zeroExtend_dist (n m : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    dist (zeroExtend n m x) (zeroExtend n m y) = dist x y := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  simp [zeroExtend, Fin.sum_univ_add]

theorem colorable_of_dimension_le {n d k : ℕ} (hnd : n ≤ d)
    (hc : (unitDistanceGraph d).Colorable k) : (unitDistanceGraph n).Colorable k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnd
  obtain ⟨c⟩ := hc
  exact ⟨SimpleGraph.Coloring.mk (fun x => c (zeroExtend n m x)) (by
    intro x y hxy
    apply c.valid
    change dist (zeroExtend n m x) (zeroExtend n m y) = 1
    rw [zeroExtend_dist]
    exact hxy)⟩

theorem chromaticLowerBound_dimension_mono {n d : ℕ} {b : ℝ}
    (hnd : n ≤ d) (h : ChromaticLowerBound n b) : ChromaticLowerBound d b := by
  intro k hc
  exact h k (colorable_of_dimension_le hnd hc)

theorem dyadic_layer_cover (q : ℕ) (hq : 0 < q) :
    ∃ ell : ℕ, 150*q ≤ 2*2^ell-1 ∧ 2*2^ell-1 ≤ 300*q+1 := by
  have hex : ∃ ell : ℕ, 150*q ≤ 2*2^ell-1 := by
    refine ⟨150*q+1, ?_⟩
    have h := Nat.lt_two_pow_self (n := 150*q+1)
    omega
  let ell := Nat.find hex
  have hlo : 150*q ≤ 2*2^ell-1 := Nat.find_spec hex
  have he : ell ≠ 0 := by
    intro h
    rw [h] at hlo
    norm_num at hlo
    omega
  obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero he
  have hp : ¬150*q ≤ 2*2^l-1 := Nat.find_min hex (by dsimp [ell] at hl; omega)
  refine ⟨ell, hlo, ?_⟩
  rw [hl, pow_succ]
  omega

end HoffmanChromatic
