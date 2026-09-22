import HoffmanChromatic.UniformCoefficient
import Mathlib.Analysis.SpecificLimits.Normed

/-! Summation of the rank weights without losing a factor of the dimension. -/
namespace HoffmanChromatic

open scoped BigOperators

theorem weighted_geometric_sum_le (s : ℝ) (hs : 0≤s) (hs1 : s<1) (D : ℕ) :
    (∑ r ∈ Finset.range (D+1), ((r:ℝ)+1)*s^r)≤1/(1-s)^2 := by
  have hn : ‖s‖<1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hs] using hs1
  have hh : HasSum (fun r : ℕ => ((r:ℝ)+1)*s^r) (1/(1-s)^2) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one 1 hn
  have hsum := hh.summable.sum_le_tsum (Finset.range (D+1)) (fun r _ => by positivity)
  rwa [hh.tsum_eq] at hsum

theorem weightedCount_uniform_bound (E : Polynomial ℕ) (n D : ℕ) (s H : ℝ)
    (hs : 0<s) (hs1 : s<1) (hH : 0≤H)
    (hb : ∀ k, ((E^n).coeff k:ℝ)*s^k*Real.sqrt (n:ℝ)≤H) :
    (weightedCount E n D:ℝ)*s^D*Real.sqrt (n:ℝ)≤H/(1-s)^2 := by
  classical
  have he : (weightedCount E n D:ℝ)*s^D*Real.sqrt (n:ℝ)=
      ∑ k ∈ Finset.range (D+1),
        (((D+1-k:ℕ):ℝ)*s^(D-k))*(((E^n).coeff k:ℝ)*s^k*Real.sqrt (n:ℝ)) := by
    unfold weightedCount
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkD : k≤D := by have := Finset.mem_range.mp hk; omega
    have hp : s^D=s^(D-k)*s^k := by rw [← pow_add, Nat.sub_add_cancel hkD]
    rw [hp]
    ring
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range (D+1), (((D+1-k:ℕ):ℝ)*s^(D-k))*H := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (hb k) (by positivity)
    _ = H*∑ r ∈ Finset.range (D+1), ((r:ℝ)+1)*s^r := by
      rw [← Finset.sum_mul, mul_comm]
      congr 1
      have href := Finset.sum_range_reflect (fun r : ℕ => ((r:ℝ)+1)*s^r) (D+1)
      rw [← href]
      apply Finset.sum_congr rfl
      intro k hk
      have hkD : k≤D := by have := Finset.mem_range.mp hk; omega
      have hidx : D+1-1-k=D-k := by omega
      have hw : D+1-k=(D-k)+1 := by omega
      simp only [hidx,hw,Nat.cast_add,Nat.cast_one]
    _ ≤ H*(1/(1-s)^2) := mul_le_mul_of_nonneg_left (weighted_geometric_sum_le s hs.le hs1 D) hH
    _ = _ := by ring

theorem uniform_weighted_coefficient_bound {A : Type*} [Fintype A]
    (b : A → ℕ) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀≤n → ∀ s : ℝ,
    ε≤s → s<1 → ∀ D : ℕ,
    (weightedCount (countPolynomial01 b) n D:ℝ)*s^D*Real.sqrt (n:ℝ)≤
      C*(partition01 b s)^n/(1-s)^2 := by
  obtain ⟨c,C,hc,hC,n₀,hbound⟩ := uniform_coefficient_bounds b ε hε hε1
  refine ⟨C,hC,n₀,?_⟩
  intro n hn s hεs hs1 D
  have hs : 0<s := hε.trans_le hεs
  exact weightedCount_uniform_bound (countPolynomial01 b) n D s (C*(partition01 b s)^n)
    hs hs1 (mul_pos hC (pow_pos (partition01_pos b s hs.le) n)).le
    (fun k => (hbound n hn s hεs hs1.le k).1)

end HoffmanChromatic
