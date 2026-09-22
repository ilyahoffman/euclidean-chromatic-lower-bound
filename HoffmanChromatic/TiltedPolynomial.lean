import HoffmanChromatic.MixturePolynomial
import HoffmanChromatic.CoefficientEstimates

/-! Exponential tilting, expressed as an exact polynomial identity. -/
namespace HoffmanChromatic

open scoped BigOperators
open Polynomial

variable {A : Type*} [Fintype A]

noncomputable def countPolynomial01 (b : A → ℕ) : Polynomial ℕ :=
  1+X+∑ j, X^(b j)

noncomputable def partition01 (b : A → ℕ) (x : ℝ) : ℝ :=
  1+x+∑ j, x^(b j)

noncomputable def mean01 (b : A → ℕ) (x : ℝ) : ℝ :=
  (x+∑ j, (b j:ℝ)*x^(b j))/partition01 b x

theorem partition01_pos (b : A → ℕ) (x : ℝ) (hx : 0≤x) : 0<partition01 b x := by
  have hs : 0≤∑ j, x^(b j) := Finset.sum_nonneg fun _ _ => pow_nonneg hx _
  dsimp [partition01]
  linarith

theorem countPolynomial01_eval (b : A → ℕ) (x : ℝ) :
    natEval (countPolynomial01 b) x=partition01 b x := by
  simp [countPolynomial01, partition01, natEval, eval₂_finset_sum]

noncomputable def tiltedRecordLaw (b : A → ℕ) (x : ℝ) (hx : 0≤x) : FiniteLaw (Option A) where
  weight := fun j => match j with
    | none => (1+x)/partition01 b x
    | some j => x^(b j)/partition01 b x
  nonneg := by
    intro j
    cases j <;> exact div_nonneg (by positivity) (partition01_pos b x hx).le
  total := by
    rw [Fintype.sum_option]
    simp only [← Finset.sum_div]
    rw [← add_div]
    exact div_self (partition01_pos b x hx).ne'

noncomputable def bernoulliParameter (x : ℝ) : ℝ := x/(1+x)

theorem tiltedRecord_mean (b : A → ℕ) (x : ℝ) (hx : 0≤x) :
    recordMean (tiltedRecordLaw b x hx) b (bernoulliParameter x)=mean01 b x := by
  have hx1 : 1+x≠0 := by positivity
  have hz : partition01 b x≠0 := (partition01_pos b x hx).ne'
  simp only [recordMean, FiniteLaw.mean, Fintype.sum_option, tiltedRecordLaw,
    recordValue, recordZero, Nat.cast_zero, Nat.cast_one, mul_one, zero_add, mul_zero, add_zero]
  simp only [mean01, bernoulliParameter]
  have hsum : (∑ j, x^(b j)/partition01 b x*(b j:ℝ))=
      (∑ j, (b j:ℝ)*x^(b j))/partition01 b x := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  field_simp
  ring

theorem tiltedRecord_polynomial (b : A → ℕ) (x : ℝ) (hx : 0≤x) :
    mixturePolynomial (tiltedRecordLaw b x hx) b (bernoulliParameter x)=
      C (1/partition01 b x)*((countPolynomial01 b).map (Nat.castRingHom ℝ)).comp (C x*X) := by
  have hx1 : 1+x≠0 := by positivity
  have hz : partition01 b x≠0 := (partition01_pos b x hx).ne'
  have hzero : (1+x)/partition01 b x*(1-bernoulliParameter x)=1/partition01 b x := by
    dsimp [bernoulliParameter]
    field_simp
    ring
  have hone : (1+x)/partition01 b x*bernoulliParameter x=x/partition01 b x := by
    dsimp [bernoulliParameter]
    field_simp
    ring
  simp only [mixturePolynomial, Fintype.sum_option, tiltedRecordLaw, recordLetterPolynomial,
    bernoulliPolynomial, mul_add, ← mul_assoc, ← map_mul, hzero, hone]
  simp only [countPolynomial01, Polynomial.map_add, Polynomial.map_one, map_X,
    Polynomial.map_sum, Polynomial.map_pow, add_comp, one_comp, X_comp, sum_comp,
    pow_comp, mul_pow, ← Polynomial.C_pow, mul_add, Finset.mul_sum, mul_one,
    ← mul_assoc, ← map_mul]
  congr 1
  · congr 2
    ring_nf
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  ring

theorem tiltedRecord_coefficient (b : A → ℕ) (x : ℝ) (hx : 0≤x) (n m : ℕ) :
    ((mixturePolynomial (tiltedRecordLaw b x hx) b (bernoulliParameter x))^n).coeff m=
      (((countPolynomial01 b)^n).coeff m:ℝ)*x^m/(partition01 b x)^n := by
  rw [tiltedRecord_polynomial, mul_pow, ← Polynomial.C_pow, ← pow_comp, coeff_C_mul,
    comp_C_mul_X_coeff]
  simp only [← Polynomial.map_pow, coeff_map, one_div_pow]
  change (1/(partition01 b x)^n)*((((countPolynomial01 b)^n).coeff m:ℝ)*x^m)=_
  ring

end HoffmanChromatic
