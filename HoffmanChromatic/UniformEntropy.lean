import HoffmanChromatic.MultinomialRate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Uniform multinomial estimates and interpolation between integer types. -/

namespace HoffmanChromatic

open scoped BigOperators

/-- An entropy estimate valid even when some multiplicities vanish. -/
theorem factorial_entropy_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    -C ≤ Real.log (n.factorial:ℝ) - (n:ℝ)*Real.log (n:ℝ) + n ∧
    Real.log (n.factorial:ℝ) - (n:ℝ)*Real.log (n:ℝ) + n ≤ C + Real.log ((n:ℝ)+1) := by
  obtain ⟨C, hC, hb⟩ := log_factorial_error_bounded
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using And.intro hC hC
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hl : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hnR
  have hm : Real.log (n:ℝ) ≤ Real.log ((n:ℝ)+1) :=
    Real.log_le_log (by linarith) (by linarith)
  have he := abs_le.mp (hb n (Nat.pos_of_ne_zero hn))
  constructor <;> nlinarith only [he.1, he.2, hl, hm]

theorem multinomial_entropy_lower {A : Type*} [Fintype A] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : A → ℕ,
      typeEntropy m - B*(Real.log ((∑ i, (m i:ℝ))+1)+1) ≤
        Real.log (Nat.multinomial Finset.univ m:ℝ) := by
  classical
  obtain ⟨C, hC, hb⟩ := factorial_entropy_bounds
  let B := (Fintype.card A:ℝ) + (Fintype.card A:ℝ)*C+C
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro m
  have hn : 0 ≤ ∑ i, (m i:ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hl : 0 ≤ Real.log ((∑ i, (m i:ℝ))+1) := Real.log_nonneg (by linarith)
  have hu : (∑ i, Real.log ((m i).factorial:ℝ)) ≤
      (∑ i, (m i:ℝ)*Real.log (m i:ℝ)) - (∑ i, (m i:ℝ)) +
        (Fintype.card A:ℝ)*(C+Real.log ((∑ i, (m i:ℝ))+1)) := by
    have hi : ∀ i, Real.log ((m i).factorial:ℝ) ≤
        (m i:ℝ)*Real.log (m i:ℝ)-(m i:ℝ) + C + Real.log ((∑ j, (m j:ℝ))+1) := by
      intro i
      have hm : (m i:ℝ) ≤ ∑ j, (m j:ℝ) := Finset.single_le_sum
        (fun j _ => Nat.cast_nonneg (m j)) (Finset.mem_univ i)
      have hh := Real.log_le_log (show (0:ℝ) < (m i:ℝ)+1 by positivity) (add_le_add_right hm 1)
      linarith [(hb (m i)).2]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
    simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_add, add_assoc] using hs
  have hd := (hb (∑ i, m i)).1
  rw [Nat.cast_sum] at hd
  rw [log_multinomial]
  unfold typeEntropy
  have hslack : 0 ≤ ((Fintype.card A:ℝ)*C+C)*Real.log ((∑ i, (m i:ℝ))+1) + (Fintype.card A:ℝ) := by positivity
  dsimp [B]
  nlinarith only [hu, hd, hslack]

noncomputable def massEntropy {A : Type*} [Fintype A] (x : A → ℝ) : ℝ :=
  -Real.negMulLog (∑ i, x i) + ∑ i, Real.negMulLog (x i)

theorem massEntropy_nat {A : Type*} [Fintype A] (m : A → ℕ) :
    massEntropy (fun i => (m i:ℝ)) = typeEntropy m := by
  simp [massEntropy, typeEntropy, Real.negMulLog, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem massEntropy_mul {A : Type*} [Fintype A] (x : A → ℝ) (c : ℝ) :
    massEntropy (fun i => c*x i) = c*massEntropy x := by
  unfold massEntropy
  rw [← Finset.mul_sum]
  simp_rw [Real.negMulLog_mul]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem massEntropy_concave_fixed_mass {A : Type*} [Fintype A]
    (x y : A → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hm : ∑ i, x i = ∑ i, y i) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a*massEntropy x+b*massEntropy y ≤ massEntropy (fun i => a*x i+b*y i) := by
  have hsum : (∑ i, (a*x i+b*y i)) = ∑ i, x i := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hm, ← add_mul, hab, one_mul]
  have hi : ∀ i, a*Real.negMulLog (x i)+b*Real.negMulLog (y i) ≤ Real.negMulLog (a*x i+b*y i) := by
    intro i
    exact Real.concaveOn_negMulLog.2 (hx i) (hy i) ha hb hab
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  unfold massEntropy
  rw [hsum, ← hm]
  have hc : (a+b)*Real.negMulLog (∑ i, x i) = Real.negMulLog (∑ i, x i) := by
    rw [hab, one_mul]
  dsimp only
  nlinarith only [h, hc]

theorem typeEntropy_mix {A : Type*} [Fintype A] (u v : A → ℕ)
    (hm : ∑ i, u i = ∑ i, v i) (p q : ℕ) :
    (p:ℝ)*typeEntropy u+(q:ℝ)*typeEntropy v ≤
      typeEntropy (fun i => p*u i+q*v i) := by
  by_cases hzero : p+q=0
  · have hp : p=0 := by omega
    have hq : q=0 := by omega
    subst p; subst q
    simp [typeEntropy]
  have ht : (0:ℝ) < (p:ℝ)+q := by exact_mod_cast Nat.pos_of_ne_zero hzero
  let a : ℝ := p/((p:ℝ)+q)
  let b : ℝ := q/((p:ℝ)+q)
  have hab : a+b=1 := by dsimp [a,b]; field_simp
  have hmR : (∑ i, (u i:ℝ)) = ∑ i, (v i:ℝ) := by exact_mod_cast hm
  have hc := massEntropy_concave_fixed_mass (fun i => (u i:ℝ)) (fun i => (v i:ℝ))
    (fun i => Nat.cast_nonneg _) (fun i => Nat.cast_nonneg _) hmR a b
    (div_nonneg (Nat.cast_nonneg _) ht.le) (div_nonneg (Nat.cast_nonneg _) ht.le) hab
  have hh := mul_le_mul_of_nonneg_left hc ht.le
  have hid : (fun i => ((p:ℝ)+q)*(a*(u i:ℝ)+b*(v i:ℝ))) =
      (fun i => ((p*u i+q*v i:ℕ):ℝ)) := by
    funext i
    dsimp [a,b]
    push_cast
    field_simp
  dsimp only at hh
  rw [← massEntropy_mul (fun i => a*(u i:ℝ)+b*(v i:ℝ)) ((p:ℝ)+q), hid,
    massEntropy_nat, massEntropy_nat, massEntropy_nat] at hh
  convert hh using 1
  dsimp [a,b]
  field_simp

end HoffmanChromatic
