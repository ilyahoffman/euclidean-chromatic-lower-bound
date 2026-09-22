import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
The integer geometry of the spherical layer, uniformly in the dimension.
This is the algebraic form of the midpoint argument in Section 2.
-/

namespace HoffmanChromatic

open scoped BigOperators

def tau (a : ℤ) : ℤ := 2 * a ^ 2 - a

def layerLevel {n : ℕ} (x : Fin n → ℤ) : ℤ := ∑ i, tau (x i)

def sqDistance {n : ℕ} (x y : Fin n → ℤ) : ℤ := ∑ i, (x i - y i) ^ 2

def midpointCorrection {n : ℕ} (x y : Fin n → ℤ) : ℤ :=
  ∑ i, (x i + y i) * (x i + y i - 1)

theorem consecutive_product_nonneg (a : ℤ) : 0 ≤ a * (a - 1) := by
  by_cases h : a ≤ 0
  · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
  · exact mul_nonneg (by omega) (by omega)

theorem midpointCorrection_nonneg {n : ℕ} (x y : Fin n → ℤ) :
    0 ≤ midpointCorrection x y := by
  exact Finset.sum_nonneg fun i _ => consecutive_product_nonneg (x i + y i)

theorem distance_decomposition {n : ℕ} (x y : Fin n → ℤ) :
    sqDistance x y = layerLevel x + layerLevel y - midpointCorrection x y := by
  unfold sqDistance layerLevel midpointCorrection tau
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sqDistance_nonneg {n : ℕ} (x y : Fin n → ℤ) : 0 ≤ sqDistance x y := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i - y i)

theorem layer_distance_bound {n : ℕ} (P : ℤ) (x y : Fin n → ℤ)
    (hx : layerLevel x = 2 * P - 1) (hy : layerLevel y = 2 * P - 1) :
    sqDistance x y ≤ 4 * P - 2 := by
  rw [distance_decomposition, hx, hy]
  have h := midpointCorrection_nonneg x y
  omega

theorem midpointCorrection_even {n : ℕ} (x y : Fin n → ℤ) :
    2 ∣ midpointCorrection x y := by
  apply Finset.dvd_sum
  intro i _
  exact (Int.even_mul_pred_self (x i + y i)).two_dvd

theorem layer_distance_even {n : ℕ} (P : ℤ) (x y : Fin n → ℤ)
    (hx : layerLevel x = 2 * P - 1) (hy : layerLevel y = 2 * P - 1) :
    2 ∣ sqDistance x y := by
  rw [distance_decomposition, hx, hy]
  have h : 2 ∣ (2 * P - 1) + (2 * P - 1) := ⟨2 * P - 1, by ring⟩
  exact dvd_sub h (midpointCorrection_even x y)

/-- Twice `rho` is the squared Euclidean distance in integer coordinates. -/
def rho {n : ℕ} (x y : Fin n → ℤ) : ℤ := sqDistance x y / 2

theorem layer_rho_spec {n : ℕ} (P : ℤ) (x y : Fin n → ℤ)
    (hx : layerLevel x = 2 * P - 1) (hy : layerLevel y = 2 * P - 1) :
    0 ≤ rho x y ∧ rho x y ≤ 2 * P - 1 ∧ 2 * rho x y = sqDistance x y := by
  have hn := sqDistance_nonneg x y
  have hb := layer_distance_bound P x y hx hy
  have he := layer_distance_even P x y hx hy
  unfold rho
  constructor
  · exact Int.ediv_nonneg hn (by norm_num)
  constructor
  · omega
  · exact Int.mul_ediv_cancel' he

theorem sqDistance_eq_zero_iff {n : ℕ} (x y : Fin n → ℤ) :
    sqDistance x y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi : (x i - y i) ^ 2 ≤ sqDistance x y := by
      exact Finset.single_le_sum (fun j _ => sq_nonneg (x j - y j)) (Finset.mem_univ i)
    rw [h] at hi
    have he : (x i - y i) ^ 2 = 0 := le_antisymm hi (sq_nonneg _)
    nlinarith [sq_nonneg (x i - y i)]
  · rintro rfl
    simp [sqDistance]

theorem quarter_sphere_identity {n : ℕ} (x : Fin n → ℤ) :
    (∑ i, (4 * x i - 1) ^ 2) = 8 * layerLevel x + n := by
  unfold layerLevel tau
  calc
    (∑ i, (4 * x i - 1) ^ 2) = ∑ i, (8 * (2 * x i ^ 2 - x i) + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp

theorem layer_rho_eq_zero_iff {n : ℕ} (P : ℤ) (x y : Fin n → ℤ)
    (hx : layerLevel x = 2 * P - 1) (hy : layerLevel y = 2 * P - 1) :
    rho x y = 0 ↔ x = y := by
  rw [← sqDistance_eq_zero_iff x y]
  have h := (layer_rho_spec P x y hx hy).2.2
  omega

def sqNorm {n : ℕ} (x : Fin n → ℤ) : ℤ := ∑ i, x i ^ 2

theorem level_sub_norm_even {n : ℕ} (x : Fin n → ℤ) :
    2 ∣ layerLevel x - sqNorm x := by
  have he : layerLevel x - sqNorm x = ∑ i, x i * (x i - 1) := by
    unfold layerLevel sqNorm tau
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  apply Finset.dvd_sum
  intro i _
  exact (Int.even_mul_pred_self (x i)).two_dvd

/-- The row factors in Section 3 have nonnegative integer exponents. -/
theorem layer_row_exponent {n : ℕ} (P : ℤ) (x : Fin n → ℤ)
    (hx : layerLevel x = 2 * P - 1) :
    ∃ r : ℕ, sqNorm x = 2 * (r : ℤ) + 1 := by
  obtain ⟨c, hc⟩ := level_sub_norm_even x
  have hn : 0 ≤ sqNorm x := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [hx] at hc
  have hr : 0 ≤ P - c - 1 := by omega
  refine ⟨(P - c - 1).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hr]
  omega

theorem distance_norm_dot {n : ℕ} (x y : Fin n → ℤ) :
    sqDistance x y = sqNorm x + sqNorm y - 2 * ∑ i, x i * y i := by
  unfold sqDistance sqNorm
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem row_exponent_identity {n : ℕ} (P : ℤ) (x y : Fin n → ℤ)
    (hx : layerLevel x = 2 * P - 1) (hy : layerLevel y = 2 * P - 1)
    (r s : ℕ) (hr : sqNorm x = 2 * (r : ℤ) + 1)
    (hs : sqNorm y = 2 * (s : ℤ) + 1) :
    rho x y - 1 = (r : ℤ) + (s : ℤ) - ∑ i, x i * y i := by
  have h := (layer_rho_spec P x y hx hy).2.2
  rw [distance_norm_dot, hr, hs] at h
  omega

end HoffmanChromatic
