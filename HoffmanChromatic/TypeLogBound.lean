import HoffmanChromatic.TypeChromatic
import HoffmanChromatic.UniformEntropy
import HoffmanChromatic.DimensionCover

/-! Logarithmic form of the finite bound for arbitrary integer types. -/
namespace HoffmanChromatic

open scoped BigOperators

noncomputable def typeScore (m : Fin 7 → ℕ) (s : ℝ) : ℝ :=
  typeEntropy m + ((typeEnergy m:ℝ)/2)*Real.log s - (typeMass m:ℝ)*Real.log (natEval countE7 s)

theorem seven_type_eval_bound (m : Fin 7 → ℕ) (r ell k : ℕ)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (he : typeEnergy m+r = 2*2^ell-1)
    (hc : (unitDistanceGraph (typeMass m+r)).Colorable k) :
    (Nat.multinomial Finset.univ m:ℝ)*s^(2^ell-1) ≤
      (k:ℝ)*(2^ell:ℕ)*(natEval countE7 s)^(typeMass m+r) := by
  have hp : 0 < (2:ℕ)^ell := pow_pos (by norm_num) _
  have hv := seven_type_coefficient_lower m 1 r
  simp only [one_mul] at hv
  rw [he] at hv
  have hnat := hv.trans (finite_seven (typeMass m+r) ell k hc)
  have hr : (Nat.multinomial Finset.univ m:ℝ) ≤
      (k:ℝ)*(weightedCount countE7 (typeMass m+r) (2^ell-1):ℝ) := by exact_mod_cast hnat
  have hw := weightedCount_eval_bound countE7 (typeMass m+r) (2^ell-1) s hs hs1
  have hP : ((2^ell-1:ℕ):ℝ)+1 = (2^ell:ℕ) := by
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ (2:ℕ)^ell from hp))
  rw [hP] at hw
  calc
    _ ≤ ((k:ℝ)*(weightedCount countE7 (typeMass m+r) (2^ell-1):ℝ))*s^(2^ell-1) :=
      mul_le_mul_of_nonneg_right hr (pow_nonneg hs.le _)
    _ = (k:ℝ)*((weightedCount countE7 (typeMass m+r) (2^ell-1):ℝ)*s^(2^ell-1)) := by ring
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg k)

theorem seven_type_log_bound (B : ℝ)
    (hb : ∀ m : Fin 7 → ℕ, typeEntropy m-B*(Real.log ((typeMass m:ℝ)+1)+1) ≤
      Real.log (Nat.multinomial Finset.univ m:ℝ))
    (m : Fin 7 → ℕ) (r ell k : ℕ) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (hE : 1 ≤ natEval countE7 s) (hr : r < 100)
    (he : typeEnergy m+r=2*2^ell-1)
    (hc : (unitDistanceGraph (typeMass m+r)).Colorable k) :
    typeScore m s - B*(Real.log ((typeMass m:ℝ)+1)+1) + 50*Real.log s -
      100*Real.log (natEval countE7 s) - Real.log ((2^ell:ℕ):ℝ) ≤ Real.log (k:ℝ) := by
  have hp : 0 < (2:ℕ)^ell := pow_pos (by norm_num) _
  have hpR : (0:ℝ) < (2^ell:ℕ) := by exact_mod_cast hp
  have hER : 0 < natEval countE7 s := lt_of_lt_of_le zero_lt_one hE
  have hm : (0:ℝ) < Nat.multinomial Finset.univ m := by exact_mod_cast Nat.multinomial_pos _ m
  have hv := seven_type_eval_bound m r ell k s hs hs1 he hc
  have hkprod := lt_of_lt_of_le (mul_pos hm (pow_pos hs _)) hv
  have hk : (0:ℝ) < k := by
    by_contra h
    have hk0 : (k:ℝ)=0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hk0] at hkprod
    simp at hkprod
  have hlog := Real.log_le_log (mul_pos hm (pow_pos hs _)) hv
  rw [Real.log_mul hm.ne' (pow_ne_zero _ hs.ne'), Real.log_pow,
    Real.log_mul (mul_ne_zero hk.ne' hpR.ne') (pow_ne_zero _ hER.ne'),
    Real.log_mul hk.ne' hpR.ne', Real.log_pow] at hlog
  have hD : (((2^ell-1:ℕ):ℝ)) = ((typeEnergy m:ℝ)+(r:ℝ)-1)/2 := by
    have hnat : 2*(2^ell-1)+1 = typeEnergy m+r := by omega
    have hh : (2:ℝ)*((2^ell-1:ℕ):ℝ)+1 = (typeEnergy m:ℝ)+(r:ℝ) := by exact_mod_cast hnat
    linarith
  have hls : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
  have hlE : 0 ≤ Real.log (natEval countE7 s) := Real.log_nonneg hE
  have hrR : (r:ℝ) ≤ 100 := by exact_mod_cast (le_of_lt hr)
  have hpad := mul_le_mul_of_nonpos_right (show ((r:ℝ)-1)/2 ≤ 50 by linarith) hls
  have hepad := mul_le_mul_of_nonneg_right hrR hlE
  rw [hD, Nat.cast_add] at hlog
  unfold typeScore
  nlinarith only [hlog, hb m, hpad, hepad]

theorem typeMass_mix (u v : Fin 7 → ℕ) (p q : ℕ) :
    typeMass (fun i => p*u i+q*v i) = p*typeMass u+q*typeMass v := by
  simp [typeMass, Finset.sum_add_distrib, Finset.mul_sum]

theorem typeEnergy_mix (u v : Fin 7 → ℕ) (p q : ℕ) :
    typeEnergy (fun i => p*u i+q*v i) = p*typeEnergy u+q*typeEnergy v := by
  simp only [typeEnergy, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem typeScore_mix (u v : Fin 7 → ℕ) (hm : typeMass u=typeMass v) (p q : ℕ) (s : ℝ) :
    (p:ℝ)*typeScore u s+(q:ℝ)*typeScore v s ≤ typeScore (fun i => p*u i+q*v i) s := by
  have h := typeEntropy_mix u v hm p q
  unfold typeScore
  rw [typeMass_mix, typeEnergy_mix]
  push_cast
  nlinarith only [h]

end HoffmanChromatic
