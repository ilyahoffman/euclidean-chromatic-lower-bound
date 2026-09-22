import Mathlib.Data.Matrix.Rank
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-! The finite-graph rank-to-colouring bridge used in Section 1. -/

namespace HoffmanChromatic

open scoped BigOperators

variable {K V : Type*} [Field K] [Fintype V]

theorem rank_submatrix_mono {m n a b : Type*}
    [Fintype m] [Fintype n] [Fintype a] [Fintype b]
    (M : Matrix m n K) (r : a → m) (c : b → n) :
    (M.submatrix r c).rank ≤ M.rank := by
  have hfin : M.eRank ≠ ⊤ := by
    intro h
    have hb := M.eRank_le_card_width
    rw [h, ENat.card_eq_coe_fintype_card] at hb
    simp at hb
  have h := ENat.toNat_le_toNat (M.eRank_submatrix_le r c) hfin
  simpa using h

theorem colorClass_card_le_rank {α : Type*} [DecidableEq α] (G : SimpleGraph V)
    (M : Matrix V V K) (hdiag : ∀ x, M x x = 1)
    (hoff : ∀ x y, x ≠ y → ¬ G.Adj x y → M x y = 0)
    (c : G.Coloring α) (a : α) :
    Fintype.card {x : V // c x = a} ≤ M.rank := by
  classical
  let S := {x : V // c x = a}
  let r : S → V := Subtype.val
  have hid : M.submatrix r r = (1 : Matrix S S K) := by
    ext x y
    by_cases h : x = y
    · subst y
      simp [Matrix.submatrix_apply, r, hdiag]
    · have hxy : x.val ≠ y.val := fun hxy => h (Subtype.ext hxy)
      have hn : ¬ G.Adj x.val y.val := by
        intro he
        exact c.valid he (x.property.trans y.property.symm)
      simp [Matrix.submatrix_apply, Matrix.one_apply, r, h, hoff _ _ hxy hn]
  have hb := rank_submatrix_mono M r r
  rw [hid, Matrix.rank_one] at hb
  exact hb

theorem card_le_colors_mul_rank {α : Type*} [Fintype α] (G : SimpleGraph V)
    (M : Matrix V V K) (hdiag : ∀ x, M x x = 1)
    (hoff : ∀ x y, x ≠ y → ¬ G.Adj x y → M x y = 0)
    (c : G.Coloring α) : Fintype.card V ≤ Fintype.card α * M.rank := by
  classical
  have hc : Fintype.card V = ∑ a : α, Fintype.card {x : V // c x = a} := by
    rw [← Fintype.card_sigma]
    exact (Fintype.card_congr (Equiv.sigmaFiberEquiv c)).symm
  rw [hc]
  calc
    (∑ a : α, Fintype.card {x : V // c x = a}) ≤ ∑ _a : α, M.rank := by
      exact Finset.sum_le_sum fun a _ => colorClass_card_le_rank G M hdiag hoff c a
    _ = Fintype.card α * M.rank := by simp

end HoffmanChromatic
