import HoffmanChromatic.CoefficientRatio

/-! The uniform coefficient argument applied to the actual Euclidean graphs. -/
namespace HoffmanChromatic

def tailA6 : Fin 4 → ℕ := ![3,6,10,15]
def tailA7 : Fin 5 → ℕ := ![3,6,10,15,21]
def tailE6 : Fin 4 → ℕ := ![3,4,8,9]
def tailE7 : Fin 5 → ℕ := ![3,4,8,9,11]

theorem count01_A6 : countPolynomial01 tailA6=countA6 := by
  simp [countPolynomial01,tailA6,Fin.sum_univ_succ,countA6]
  ring
theorem count01_A7 : countPolynomial01 tailA7=countA7 := by
  simp [countPolynomial01,tailA7,Fin.sum_univ_succ,countA7,countA6]
  ring
theorem count01_E6 : countPolynomial01 tailE6=countE6 := by
  simp [countPolynomial01,tailE6,Fin.sum_univ_succ,countE6]
  ring
theorem count01_E7 : countPolynomial01 tailE7=countE7 := by
  simp [countPolynomial01,tailE7,Fin.sum_univ_succ,countE7,countE6]
  ring

theorem partition01_A6 (t : ℝ) : partition01 tailA6 t=realA6 t := by
  simp [partition01,tailA6,Fin.sum_univ_succ,realA6]
  ring
theorem partition01_A7 (t : ℝ) : partition01 tailA7 t=realA7 t := by
  simp [partition01,tailA7,Fin.sum_univ_succ,realA7,realA6]
  ring
theorem partition01_E6 (s : ℝ) : partition01 tailE6 s=realE6 s := by
  simp [partition01,tailE6,Fin.sum_univ_succ,realE6]
  ring
theorem partition01_E7 (s : ℝ) : partition01 tailE7 s=realE7 s := by
  simp [partition01,tailE7,Fin.sum_univ_succ,realE7,realE6]
  ring

theorem six_uniform_parameter_bound (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    ∃ q : ℝ, 0<q ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀≤n → ∀ ell : ℕ, ∀ t s : ℝ,
    ε≤t → t≤1 → ε≤s → s<1 →
    |((2*2^ell-1:ℕ):ℝ)-(n:ℝ)*mean01 tailA6 t|≤1 →
    ChromaticLowerBound n
      (q*(1-s)^2*(s^(2^ell-1)/t^(2*2^ell-1))*(realA6 t/realE6 s)^n) := by
  have hf : ∀ n ell k : ℕ, (unitDistanceGraph n).Colorable k →
      ((countPolynomial01 tailA6)^n).coeff (2*2^ell-1)≤
        k*weightedCount (countPolynomial01 tailE6) n (2^ell-1) := by
    simpa only [count01_A6,count01_E6] using finite_six
  simpa only [partition01_A6,partition01_E6] using
    uniform_polynomial_chromatic_bound tailA6 tailE6 ε hε hε1 hf

theorem seven_uniform_parameter_bound (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    ∃ q : ℝ, 0<q ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀≤n → ∀ ell : ℕ, ∀ t s : ℝ,
    ε≤t → t≤1 → ε≤s → s<1 →
    |((2*2^ell-1:ℕ):ℝ)-(n:ℝ)*mean01 tailA7 t|≤1 →
    ChromaticLowerBound n
      (q*(1-s)^2*(s^(2^ell-1)/t^(2*2^ell-1))*(realA7 t/realE7 s)^n) := by
  have hf : ∀ n ell k : ℕ, (unitDistanceGraph n).Colorable k →
      ((countPolynomial01 tailA7)^n).coeff (2*2^ell-1)≤
        k*weightedCount (countPolynomial01 tailE7) n (2^ell-1) := by
    simpa only [count01_A7,count01_E7] using finite_seven
  simpa only [partition01_A7,partition01_E7] using
    uniform_polynomial_chromatic_bound tailA7 tailE7 ε hε hε1 hf

end HoffmanChromatic
