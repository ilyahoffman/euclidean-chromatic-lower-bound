import HoffmanChromatic.CoefficientEstimates
import HoffmanChromatic.TypeGrowth

/-! Fixed types and bounded strings of ones on power-of-two layers. -/

namespace HoffmanChromatic

open scoped BigOperators Topology
open Filter

def sevenWeight (i : Fin 7) : ℕ := letterWeight (intervalLetter (-3) i)
def typeMass (m : Fin 7 → ℕ) : ℕ := ∑ i, m i
def typeEnergy (m : Fin 7 → ℕ) : ℕ := ∑ i, sevenWeight i*m i

theorem seven_type_coefficient_lower (m : Fin 7 → ℕ) (q r : ℕ) :
    Nat.multinomial Finset.univ (fun i => q*m i) ≤
      (countA7^(q*typeMass m+r)).coeff (q*typeEnergy m+r) := by
  have hl : 1 ≤ (weightPolynomial sevenWeight).coeff 1 := by
    change 1 ≤ (weightPolynomial (fun j : Fin 7 => letterWeight (intervalLetter (-3) j))).coeff 1
    rw [alphabet_seven_count]
    norm_num [countA7, countA6]
  have h := type_with_ones_lower sevenWeight m hl q r
  change Nat.multinomial Finset.univ (fun i => q*m i) ≤
    ((weightPolynomial (fun j : Fin 7 => letterWeight (intervalLetter (-3) j)))^
      (q*typeMass m+r)).coeff (q*typeEnergy m+r) at h
  rw [alphabet_seven_count] at h
  exact h

theorem seven_type_normalized_bound (m : Fin 7 → ℕ) (q r ell k : ℕ)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (he : q*typeEnergy m+r = 2*2^ell-1)
    (hc : (unitDistanceGraph (q*typeMass m+r)).Colorable k) :
    (Nat.multinomial Finset.univ (fun i => q*m i):ℝ)*t^(q*typeEnergy m+r) ≤
      (k:ℝ)*(2^ell:ℕ)*t*(natEval countE7 (t^2))^(q*typeMass m+r) := by
  have hp : 0 < (2:ℕ)^ell := pow_pos (by norm_num) _
  have hv := seven_type_coefficient_lower m q r
  rw [he] at hv
  have hnat := hv.trans (finite_seven (q*typeMass m+r) ell k hc)
  have hr : (Nat.multinomial Finset.univ (fun i => q*m i):ℝ) ≤
      (k:ℝ)*(weightedCount countE7 (q*typeMass m+r) (2^ell-1):ℝ) := by
    exact_mod_cast hnat
  have hw := weightedCount_eval_bound countE7 (q*typeMass m+r) (2^ell-1) (t^2)
    (pow_pos ht _) (pow_le_one₀ ht.le ht1)
  have hP : ((2^ell-1:ℕ):ℝ)+1 = (2^ell:ℕ) := by
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ (2:ℕ)^ell from hp))
  rw [hP] at hw
  have hexp : q*typeEnergy m+r = 2*(2^ell-1)+1 := by rw [he]; omega
  calc
    _ = t*((Nat.multinomial Finset.univ (fun i => q*m i):ℝ)*(t^2)^(2^ell-1)) := by
      rw [hexp, pow_succ, pow_mul]
      ring
    _ ≤ t*(((k:ℝ)*(weightedCount countE7 (q*typeMass m+r) (2^ell-1):ℝ))*(t^2)^(2^ell-1)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr (by positivity)) ht.le
    _ = (k:ℝ)*t*((weightedCount countE7 (q*typeMass m+r) (2^ell-1):ℝ)*(t^2)^(2^ell-1)) := by ring
    _ ≤ (k:ℝ)*t*((2^ell:ℕ)*(natEval countE7 (t^2))^(q*typeMass m+r)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

theorem fixed_type_subsequence (m : Fin 7 → ℕ) (t C : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 < C)
    (hE : 0 < natEval countE7 (t^2)) (hM : 0 < typeMass m) (hK : 0 < typeEnergy m)
    (hmargin : 0 < typeEntropy m + (typeEnergy m:ℝ)*Real.log t -
      (typeMass m:ℝ)*Real.log (C*natEval countE7 (t^2))) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ChromaticLowerBound n (C^n) := by
  classical
  let K := typeEnergy m
  let M := typeMass m
  let E := natEval countE7 (t^2)
  have hg : ∀ r : Fin K, ∀ᶠ q : ℕ in atTop,
      t*((q*K+r.val+1:ℕ):ℝ)*(C*E)^(q*M+r.val) <
        (Nat.multinomial Finset.univ (fun i => q*m i):ℝ)*t^(q*K+r.val) := by
    intro r
    apply fixed_type_exponential_margin m K r.val t (C*E) t ht (mul_pos hC hE) ht
    simpa only [typeMass, Nat.cast_sum] using hmargin
  have hgall := Filter.eventually_all.mpr hg
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp hgall
  intro N
  let B := max q₀ N + 1
  let ell := B*K+1
  let P := 2^ell
  let S := 2*P-1
  let q := S/K
  let r := S%K
  have hp : 0 < P := pow_pos (by norm_num) _
  have hpow : ell < P := Nat.lt_two_pow_self
  have hB : B*K ≤ S := by dsimp [ell, S] at *; omega
  have hqB : B ≤ q := (Nat.le_div_iff_mul_le hK).2 hB
  have hr : r < K := Nat.mod_lt S hK
  have he : q*K+r = 2*P-1 := by
    dsimp [q, r, S]
    simpa only [Nat.mul_comm] using Nat.div_add_mod (2*P-1) K
  have hqn : N ≤ q := by dsimp [B] at hqB; omega
  have hq0 : q₀ ≤ q := by dsimp [B] at hqB; omega
  have hn : N ≤ q*M+r := by
    exact hqn.trans ((Nat.le_mul_of_pos_right q hM).trans (Nat.le_add_right _ _))
  refine ⟨q*M+r, hn, ?_⟩
  intro k hc
  have hlow := hq₀ q hq0 ⟨r, hr⟩
  have hupp := seven_type_normalized_bound m q r ell k t ht ht1 he hc
  have hP : P ≤ q*K+r+1 := by omega
  have hscale : 0 < (P:ℝ)*t*E^(q*M+r) := mul_pos (mul_pos (by exact_mod_cast hp) ht) (pow_pos hE _)
  have hthreshold : C^(q*M+r)*((P:ℝ)*t*E^(q*M+r)) ≤
      t*((q*K+r+1:ℕ):ℝ)*(C*E)^(q*M+r) := by
    rw [mul_pow]
    calc
      _ = t*(P:ℝ)*(C^(q*M+r)*E^(q*M+r)) := by ring
      _ ≤ _ := by
        gcongr
  have hstrict := hthreshold.trans_lt hlow
  have hupp' : (Nat.multinomial Finset.univ (fun i => q*m i):ℝ)*t^(q*K+r) ≤
      (k:ℝ)*((P:ℝ)*t*E^(q*M+r)) := by
    convert hupp using 1
    ring
  have hproduct := hstrict.trans_le hupp'
  nlinarith only [hproduct, hscale]

end HoffmanChromatic
