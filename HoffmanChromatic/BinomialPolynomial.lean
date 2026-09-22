import HoffmanChromatic.BinomialMode
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Nat.Choose.Sum

/-! Exact generating-function identities, including negative coefficient indices. -/
namespace HoffmanChromatic
open scoped BigOperators
open Polynomial

noncomputable def bernoulliPolynomial (t : ℝ) : Polynomial ℝ := C (1-t)+C t*X

theorem bernoulliPolynomial_coeff_pow (n k : ℕ) (t : ℝ) :
    ((bernoulliPolynomial t)^n).coeff k=binomialMass n k t := by
  have h : ((X+C (1-t))^n).comp (C t*X)=(bernoulliPolynomial t)^n := by
    simp only [pow_comp, add_comp, X_comp, C_comp, bernoulliPolynomial, add_comm]
  rw [← h, comp_C_mul_X_coeff, coeff_X_add_C_pow]
  unfold binomialMass
  ring

theorem binomialMass_nonneg (n k : ℕ) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    0≤binomialMass n k t := by
  unfold binomialMass
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht _)) (pow_nonneg (by linarith) _)

theorem binomialMass_sum (n : ℕ) (t : ℝ) :
    (∑ k ∈ Finset.range (n+1), binomialMass n k t)=1 := by
  have h := add_pow t (1-t) n
  have ht : t+(1-t)=1 := by ring
  rw [ht, one_pow] at h
  simpa only [binomialMass, mul_comm, mul_left_comm, mul_assoc] using h.symm

theorem binomialMass_le_one (n k : ℕ) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    binomialMass n k t≤1 := by
  by_cases hk : k≤n
  · have h := Finset.single_le_sum (s := Finset.range (n+1))
      (f := fun j => binomialMass n j t) (fun j _ => binomialMass_nonneg n j ht ht1)
      (show k∈Finset.range (n+1) by simp; omega)
    rwa [binomialMass_sum] at h
  · simp [binomialMass, Nat.choose_eq_zero_of_lt (show n<k by omega)]

noncomputable def binomialMassZ (n : ℕ) (k : ℤ) (t : ℝ) : ℝ :=
  if 0≤k then binomialMass n k.toNat t else 0

theorem binomialMassZ_nat (n k : ℕ) (t : ℝ) : binomialMassZ n (k:ℤ) t=binomialMass n k t := by
  simp [binomialMassZ]

theorem binomialMassZ_nonneg (n : ℕ) (k : ℤ) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    0≤binomialMassZ n k t := by
  unfold binomialMassZ
  split_ifs
  · exact binomialMass_nonneg _ _ ht ht1
  · exact le_rfl

theorem binomialMassZ_le_one (n : ℕ) (k : ℤ) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    binomialMassZ n k t≤1 := by
  unfold binomialMassZ
  split_ifs
  · exact binomialMass_le_one _ _ ht ht1
  · norm_num

theorem shifted_bernoulli_coeff (n R m : ℕ) (t : ℝ) :
    (X^R*(bernoulliPolynomial t)^n).coeff m=binomialMassZ n ((m:ℤ)-R) t := by
  rw [coeff_X_pow_mul']
  unfold binomialMassZ
  by_cases h : R≤m
  · have hz : (0:ℤ)≤(m:ℤ)-R := by omega
    rw [if_pos h, if_pos hz, bernoulliPolynomial_coeff_pow]
    have ht : ((m:ℤ)-R).toNat=m-R := by omega
    rw [ht]
  · have hz : ¬(0:ℤ)≤(m:ℤ)-R := by omega
    rw [if_neg h, if_neg hz]

/-- The central binomial estimate with an arbitrary integer index. -/
theorem binomial_central_bounds_Z (a A : ℝ) (ha : 0<a) (hA : 0≤A) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ k : ℤ, ∀ t : ℝ,
      a≤t → t≤1-a → |(k:ℝ)-(n:ℝ)*t|≤A*Real.sqrt (n:ℝ) →
      c≤binomialMassZ n k t*Real.sqrt (n:ℝ) ∧ binomialMassZ n k t*Real.sqrt (n:ℝ)≤C := by
  obtain ⟨c,C,hc,hC,N,hb⟩ := binomial_central_bounds a A ha hA
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge (A^2/a^2+1)
  refine ⟨c,C,hc,hC,max N N₁, ?_⟩
  intro n hn k t hat hta hwin
  have hk : 0≤k := by
    by_contra hk
    have hkR : (k:ℝ)<0 := by exact_mod_cast (lt_of_not_ge hk)
    have hnN : (N₁:ℝ)≤n := by exact_mod_cast (show N₁≤n by omega)
    have hnR : (0:ℝ)<n := by
      have hq : 0≤A^2/a^2 := by positivity
      linarith
    have hlarge : A^2<a^2*(n:ℝ) := by
      have hd : A^2/a^2<(n:ℝ) := by linarith
      have hh := (div_lt_iff₀ (sq_pos_of_pos ha)).mp hd
      nlinarith only [hh]
    have hprod := mul_lt_mul_of_pos_right hlarge hnR
    have htR := mul_le_mul_of_nonneg_left hat hnR.le
    have hneg : (k:ℝ)-(n:ℝ)*t<0 := by nlinarith only [hkR, htR, mul_pos hnR ha]
    rw [abs_of_neg hneg] at hwin
    have hh : a*(n:ℝ)≤A*Real.sqrt (n:ℝ) := by linarith only [hwin, htR, hkR]
    have hsq := mul_self_le_mul_self (mul_nonneg ha.le hnR.le) hh
    have hsq' : a^2*(n:ℝ)^2≤A^2*(n:ℝ) := by
      simpa only [← sq, mul_pow, Real.sq_sqrt hnR.le] using hsq
    nlinarith only [hsq', hprod]
  have hkcast : (k.toNat:ℝ)=(k:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk
  unfold binomialMassZ
  rw [if_pos hk]
  apply hb n (by omega) k.toNat t hat hta
  simpa only [hkcast] using hwin

end HoffmanChromatic
