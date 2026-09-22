import Mathlib.Data.Matrix.Rank
import Mathlib.RingTheory.PowerSeries.Basic

/-!
Coefficient-rank transfer over an arbitrary field.  The proof explicitly
factors the coefficient matrix through the finite set of surviving pairs
`(summand, coefficient index)`.  No generic-rank assumption is used.
-/

namespace HoffmanChromatic

open scoped BigOperators

variable {K : Type*} [Field K]

/-- The product expansion behind tensoring the one-coordinate factorization. -/
theorem product_separated
    {R A J : Type*} [CommSemiring R] [Fintype J]
    (w : R) (l : J → ℕ) (B : A → A → R) (u v : J → A → R)
    (hB : ∀ a b, B a b = ∑ j, w^l j * (u j a * v j b))
    (n : ℕ) (x y : Fin n → A) :
    (∏ i, B (x i) (y i)) =
      ∑ j : Fin n → J, w^(∑ i, l (j i)) *
        ((∏ i, u (j i) (x i)) * (∏ i, v (j i) (y i))) := by
  classical
  simp_rw [hB]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem coeff_shifted_product (D l : ℕ) (u v : PowerSeries K) :
    PowerSeries.coeff K D (PowerSeries.X ^ l * (u * v)) =
      ∑ r : Fin (D + 1 - l),
        PowerSeries.coeff K r.val u * PowerSeries.coeff K (D - l - r.val) v := by
  rw [PowerSeries.coeff_X_pow_mul']
  rw [Finset.sum_fin_eq_sum_range]
  by_cases h : l ≤ D
  · rw [if_pos h]
    have hn : D + 1 - l = (D - l) + 1 := by omega
    simp only [hn, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [dif_pos (Finset.mem_range.mp hr)]
  · rw [if_neg h]
    have hn : D + 1 - l = 0 := by omega
    simp [hn]

noncomputable def coefficientMatrix {m n : Type*} (D : ℕ) (F : Matrix m n (PowerSeries K)) :
    Matrix m n K := fun a b => PowerSeries.coeff K D (F a b)

theorem coefficient_rank_transfer
    {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι]
    (D : ℕ) (l : ι → ℕ)
    (u : ι → m → PowerSeries K) (v : ι → n → PowerSeries K) :
    (coefficientMatrix D (fun a b =>
      ∑ i, PowerSeries.X ^ l i * (u i a * v i b))).rank ≤
        ∑ i, (D + 1 - l i) := by
  classical
  let J := (i : ι) × Fin (D + 1 - l i)
  let L : Matrix m J K := fun a j => PowerSeries.coeff K j.2.val (u j.1 a)
  let R : Matrix J n K := fun j b =>
    PowerSeries.coeff K (D - l j.1 - j.2.val) (v j.1 b)
  have hf : coefficientMatrix D (fun a b =>
      ∑ i, PowerSeries.X ^ l i * (u i a * v i b)) = L * R := by
    ext a b
    simp only [coefficientMatrix, map_sum, Matrix.mul_apply, Fintype.sum_sigma,
      coeff_shifted_product, L, R, J]
  rw [hf]
  calc
    (L * R).rank ≤ L.rank := Matrix.rank_mul_le_left L R
    _ ≤ Fintype.card J := Matrix.rank_le_card_width L
    _ = ∑ i, (D + 1 - l i) := by simp [J, Fintype.card_sigma]

/-- Tensoring, restricting rows, and absorbing row/column series before extraction. -/
theorem tensor_coefficient_rank_bound
    {A J V : Type*} [Fintype J] [Fintype V]
    (n D : ℕ) (l : J → ℕ) (B : A → A → PowerSeries K)
    (u v : J → A → PowerSeries K)
    (hB : ∀ a b, B a b = ∑ j, PowerSeries.X^l j * (u j a * v j b))
    (coord : V → Fin n → A) (left right : V → PowerSeries K) :
    (coefficientMatrix D (fun x y =>
      left x * (∏ i, B (coord x i) (coord y i)) * right y)).rank ≤
        ∑ j : Fin n → J, (D + 1 - ∑ i, l (j i)) := by
  have hf : (fun x y => left x * (∏ i, B (coord x i) (coord y i)) * right y) =
      (fun x y => ∑ j : Fin n → J, PowerSeries.X^(∑ i, l (j i)) *
        ((left x * ∏ i, u (j i) (coord x i)) *
          ((∏ i, v (j i) (coord y i)) * right y))) := by
    funext x y
    rw [product_separated PowerSeries.X l B u v hB, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ac_rfl
  rw [hf]
  exact coefficient_rank_transfer D (fun j : Fin n → J => ∑ i, l (j i))
    (fun j x => left x * ∏ i, u (j i) (coord x i))
    (fun j y => (∏ i, v (j i) (coord y i)) * right y)

end HoffmanChromatic
