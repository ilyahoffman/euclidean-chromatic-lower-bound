import HoffmanChromatic.EuclideanBridge
import HoffmanChromatic.Detector
import HoffmanChromatic.Counting
import Mathlib.Algebra.Field.ZMod

/-!
The actual detector on an arbitrary finite alphabet of distinct integers.
There are no hypotheses about the detector entries in the final theorem:
the diagonal and nonedge conditions are derived from the spherical layer.
-/

namespace HoffmanChromatic

open scoped BigOperators

theorem tau_nonneg (a : ℤ) : 0 ≤ tau a := by
  have h := consecutive_product_nonneg a
  unfold tau
  nlinarith [sq_nonneg a]

def letterWeight (a : ℤ) : ℕ := (tau a).toNat

@[simp] theorem letterWeight_cast (a : ℤ) : (letterWeight a : ℤ) = tau a :=
  Int.toNat_of_nonneg (tau_nonneg a)

abbrev SphericalLayer {A : Type*} (enc : A → ℤ) (n P : ℕ) :=
  {x : Fin n → A // ∑ i, letterWeight (enc (x i)) = 2 * P - 1}

noncomputable instance {A : Type*} [Fintype A] (enc : A → ℤ) (n P : ℕ) :
    Fintype (SphericalLayer enc n P) := by
  classical
  unfold SphericalLayer
  infer_instance

def layerPoint {A : Type*} {enc : A → ℤ} {n P : ℕ}
    (x : SphericalLayer enc n P) : Fin n → ℤ := fun i => enc (x.val i)

theorem layerPoint_level {A : Type*} {enc : A → ℤ} {n P : ℕ}
    (hP : 0 < P) (x : SphericalLayer enc n P) :
    layerLevel (layerPoint x) = 2 * (P : ℤ) - 1 := by
  have h := congrArg (fun m : ℕ => (m : ℤ)) x.property
  have hp : 1 ≤ 2 * P := by omega
  simpa [layerLevel, layerPoint, Nat.cast_sub hp, letterWeight_cast] using h

theorem layerPoint_injective {A : Type*} {enc : A → ℤ} {n P : ℕ}
    (he : Function.Injective enc) :
    Function.Injective (@layerPoint A enc n P) := by
  intro x y h
  apply Subtype.ext
  funext i
  exact he (congrFun h i)

def layerDetector {A : Type*} (enc : A → ℤ) (n ell : ℕ) :
    Matrix (SphericalLayer enc n (2^ell)) (SphericalLayer enc n (2^ell)) (ZMod 2) :=
  fun x y => binaryDetector ell (rho (layerPoint x) (layerPoint y)).toNat

theorem layerDetector_spec {A : Type*} [DecidableEq A] {enc : A → ℤ} (he : Function.Injective enc)
    (n ell : ℕ) (x y : SphericalLayer enc n (2^ell)) :
    layerDetector enc n ell x y =
      if x = y ∨ rho (layerPoint x) (layerPoint y) = (2^ell : ℕ) then 1 else 0 := by
  classical
  have hp : 0 < (2:ℕ)^ell := pow_pos (by norm_num) _
  have hx := layerPoint_level hp x
  have hy := layerPoint_level hp y
  have h := layer_rho_spec (2^ell : ℕ) (layerPoint x) (layerPoint y) hx hy
  have hn := Int.toNat_of_nonneg h.1
  have hw : (rho (layerPoint x) (layerPoint y)).toNat < 2 * 2^ell := by omega
  have hz : (rho (layerPoint x) (layerPoint y)).toNat = 0 ↔ x = y := by
    rw [← (layerPoint_injective he).eq_iff, ← layer_rho_eq_zero_iff _ _ _ hx hy]
    omega
  have heq : (rho (layerPoint x) (layerPoint y)).toNat = 2^ell ↔
      rho (layerPoint x) (layerPoint y) = (2^ell : ℕ) := by omega
  simp only [layerDetector, binaryDetector_spec ell _ hw, hz, heq]

theorem spherical_layer_card_bound {A : Type*} [Fintype A] (enc : A → ℤ)
    (he : Function.Injective enc) (n ell k : ℕ)
    (hc : (unitDistanceGraph n).Colorable k) :
    ((weightPolynomial (fun a => letterWeight (enc a)))^n).coeff (2 * 2^ell - 1) ≤
      k * (layerDetector enc n ell).rank := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : 0 < (2:ℕ)^ell := pow_pos (by norm_num) _
  let G : SimpleGraph (SphericalLayer enc n (2^ell)) :=
    SimpleGraph.comap (scaledPoint (2^ell) ∘ layerPoint) (unitDistanceGraph n)
  have hdiag : ∀ x, layerDetector enc n ell x x = 1 := by
    intro x
    rw [layerDetector_spec he]
    simp
  have hoff : ∀ x y, x ≠ y → ¬ G.Adj x y → layerDetector enc n ell x y = 0 := by
    intro x y hxy hn
    rw [layerDetector_spec he]
    have hr : rho (layerPoint x) (layerPoint y) ≠ (2^ell : ℕ) := by
      intro h
      apply hn
      have hd := (layer_rho_spec (2^ell : ℕ) _ _
        (layerPoint_level hp x) (layerPoint_level hp y)).2.2
      have hdist : sqDistance (layerPoint x) (layerPoint y) = 2 * (2^ell : ℕ) := by
        rw [h] at hd
        exact hd.symm
      change dist (scaledPoint (2^ell) (layerPoint x))
        (scaledPoint (2^ell) (layerPoint y)) = 1
      exact scaledPoint_unit_distance (2^ell) hp _ _ hdist
    exact if_neg (not_or.mpr ⟨hxy, hr⟩)
  obtain ⟨c⟩ := hc
  let cv : G.Coloring (Fin k) := SimpleGraph.Coloring.mk
    (fun x => c (scaledPoint (2^ell) (layerPoint x))) (by
      intro x y h
      exact c.valid h)
  have hb := card_le_colors_mul_rank G (layerDetector enc n ell) hdiag hoff cv
  change Fintype.card {x : Fin n → A // ∑ i, letterWeight (enc (x i)) = 2 * 2^ell - 1}
    ≤ Fintype.card (Fin k) * (layerDetector enc n ell).rank at hb
  rw [layer_card_eq_coefficient (fun a => letterWeight (enc a)) n (2 * 2^ell - 1)] at hb
  simpa only [Fintype.card_fin] using hb

end HoffmanChromatic
