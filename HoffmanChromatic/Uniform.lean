import HoffmanChromatic.UniformRate
import HoffmanChromatic.SharpCover

/-! The closed sharp uniform endpoint, for the actual Euclidean metric. -/
namespace HoffmanChromatic

theorem dyadic_real_cover (x : ℝ) (hx : 1<x) :
    ∃ ell : ℕ, x≤(2^ell:ℕ) ∧ (2^ell:ℕ)<2*x := by
  have hex : ∃ ell : ℕ, x≤(2^ell:ℕ) := by
    obtain ⟨M,hM⟩ := exists_nat_ge x
    refine ⟨M,hM.trans ?_⟩
    exact_mod_cast (Nat.lt_two_pow_self (n := M)).le
  let ell := Nat.find hex
  have hlo : x≤(2^ell:ℕ) := Nat.find_spec hex
  have he : ell≠0 := by
    intro he
    rw [he] at hlo
    norm_num at hlo
    linarith
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero he
  have hp : ¬x≤(2^j:ℕ) := Nat.find_min hex (by dsimp [ell] at hj; omega)
  refine ⟨ell,hlo,?_⟩
  rw [hj,pow_succ]
  push_cast
  have hlt := lt_of_not_ge hp
  push_cast at hlt
  linarith only [hlt]

theorem uniform_chromatic : UniformTarget := by
  obtain ⟨a,ha,huniq,hbaseL,hbaseU,hheight⟩ := sharp_crossing
  obtain ⟨c6,hc6,N6,h6⟩ := six_uniform_rate
  obtain ⟨c7,hc7,N7,h7⟩ := seven_uniform_rate
  have hcover := sharp_rate_cover a ha hheight
  refine ⟨a,ha,huniq,hbaseL,hbaseU,min c6 c7,lt_min hc6 hc7,max 4 (max N6 N7),?_⟩
  intro n hn
  have hn4 : 4≤n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn4R : (4:ℝ)≤n := by exact_mod_cast hn4
  have haL := ha.1
  have haU := ha.2.1
  have hlarge : 1<a*(n:ℝ) := by nlinarith only [haL,hn4R]
  obtain ⟨ell,hP,hP2⟩ := dyadic_real_cover (a*(n:ℝ)) hlarge
  let δ : ℝ := (2^ell:ℕ)/(n:ℝ)
  have hδL : a≤δ := (le_div_iff₀ hnR).2 hP
  have hδU : δ<2*a := by
    apply (div_lt_iff₀ hnR).2
    nlinarith only [hP2]
  have hK1 : (37/100:ℝ)≤δ := by linarith only [haL,hδL]
  have hK2 : δ≤3/4 := by linarith only [haU,hδU]
  have he : (Real.exp (delta6 a))^n=Real.exp ((n:ℝ)*delta6 a) := (Real.exp_nat_mul _ _).symm
  rw [he]
  by_cases hδ : δ≤11/20
  · have hr := hcover.1 δ hδL hδ
    have hbound := h6 n (by omega) ell hK1 hK2
    have hx := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr hnR.le)
    intro k hk
    calc
      min c6 c7*Real.exp ((n:ℝ)*delta6 a) ≤ c6*Real.exp ((n:ℝ)*delta6 δ) :=
        mul_le_mul (min_le_left _ _) hx (Real.exp_pos _).le hc6.le
      _ ≤ (k:ℝ) := hbound k hk
  · have hr := hcover.2 δ (le_of_not_ge hδ) hδU.le
    have hbound := h7 n (by omega) ell hK1 hK2
    have hx := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr hnR.le)
    intro k hk
    calc
      min c6 c7*Real.exp ((n:ℝ)*delta6 a) ≤ c7*Real.exp ((n:ℝ)*delta7 δ) :=
        mul_le_mul (min_le_right _ _) hx (Real.exp_pos _).le hc7.le
      _ ≤ (k:ℝ) := hbound k hk

end HoffmanChromatic
