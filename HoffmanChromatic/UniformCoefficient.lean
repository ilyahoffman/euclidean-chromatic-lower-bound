import HoffmanChromatic.MixtureCoefficient
import HoffmanChromatic.TiltedPolynomial

/-! Uniform local bounds for coefficients of powers of a fixed polynomial. -/
namespace HoffmanChromatic

open scoped BigOperators

variable {A : Type*} [Fintype A]

theorem partition01_le_card (b : A → ℕ) (x : ℝ) (hx : 0≤x) (hx1 : x≤1) :
    partition01 b x≤(Fintype.card A:ℝ)+2 := by
  have hs : (∑ j, x^(b j))≤(Fintype.card A:ℝ) := by
    calc
      _ ≤ ∑ _j : A, (1:ℝ) := Finset.sum_le_sum fun j _ => pow_le_one₀ hx hx1
      _ = _ := by simp
  dsimp [partition01]
  linarith

/-- The numerator and denominator of the chromatic estimate have the same
`n^(-1/2)` factor.  The lower estimate is local; the upper estimate holds
at every coefficient index. -/
theorem uniform_coefficient_bounds (b : A → ℕ) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀≤n → ∀ x : ℝ,
    ε≤x → x≤1 → ∀ m : ℕ,
    (((countPolynomial01 b)^n).coeff m:ℝ)*x^m*Real.sqrt (n:ℝ)≤C*(partition01 b x)^n ∧
    (|(m:ℝ)-(n:ℝ)*mean01 b x|≤1 →
      c*(partition01 b x)^n≤(((countPolynomial01 b)^n).coeff m:ℝ)*x^m*Real.sqrt (n:ℝ)) := by
  let a := min (ε/2) (1/((Fintype.card A:ℝ)+2))
  let B : ℝ := (∑ j, b j : ℕ)+1
  have hq : (0:ℝ)<(Fintype.card A:ℝ)+2 := by positivity
  have ha : 0<a := lt_min (by positivity) (by positivity)
  have haε : a≤ε/2 := min_le_left _ _
  have haq : a≤1/((Fintype.card A:ℝ)+2) := min_le_right _ _
  have hB : 1≤B := by
    have hh : (0:ℝ)≤(∑ j, b j:ℕ) := Nat.cast_nonneg _
    dsimp [B]
    linarith
  have hb : ∀ j, (b j:ℝ)≤B := by
    intro j
    have hh : b j≤∑ i, b i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hhR : (b j:ℝ)≤(∑ i, b i:ℕ) := by exact_mod_cast hh
    dsimp [B]
    linarith
  obtain ⟨c,C,hc,hC,n₀,hbound⟩ := mixture_coefficient_bounds a B ha hB
  refine ⟨c,C,hc,hC,n₀,?_⟩
  intro n hn x hεx hx1 m
  have hx : 0<x := hε.trans_le hεx
  have hz : 0<partition01 b x := partition01_pos b x hx.le
  have hxden : 0<1+x := by positivity
  have hα : a≤(tiltedRecordLaw b x hx.le).weight none := by
    change a≤(1+x)/partition01 b x
    have hzq := partition01_le_card b x hx.le hx1
    apply haq.trans
    apply (le_div_iff₀ hz).2
    have hh := mul_le_mul_of_nonneg_left hzq (show 0≤1/((Fintype.card A:ℝ)+2) by positivity)
    have hid : 1/((Fintype.card A:ℝ)+2)*((Fintype.card A:ℝ)+2)=1 := by field_simp
    rw [hid] at hh
    linarith
  have hat : a≤bernoulliParameter x := by
    unfold bernoulliParameter
    apply haε.trans
    apply (le_div_iff₀ hxden).2
    have hh := mul_le_mul_of_nonneg_left hx1 hε.le
    nlinarith only [hh,hεx]
  have hta : bernoulliParameter x≤1-a := by
    unfold bernoulliParameter
    apply (div_le_iff₀ hxden).2
    have ha1 : a≤1/2 := by linarith
    have hh := mul_le_mul_of_nonneg_left hx1 ha.le
    nlinarith only [hh,ha1]
  have h := hbound n hn A b (tiltedRecordLaw b x hx.le) (bernoulliParameter x) hb hα hat hta m
  rw [tiltedRecord_coefficient] at h
  have hzn : 0<(partition01 b x)^n := pow_pos hz n
  constructor
  · have hh := mul_le_mul_of_nonneg_right h.1 hzn.le
    have he : ((((countPolynomial01 b)^n).coeff m:ℝ)*x^m/(partition01 b x)^n*
        Real.sqrt (n:ℝ))*(partition01 b x)^n=
        (((countPolynomial01 b)^n).coeff m:ℝ)*x^m*Real.sqrt (n:ℝ) := by field_simp
    rwa [he] at hh
  · intro hm
    have hm' : |(m:ℝ)-(n:ℝ)*recordMean (tiltedRecordLaw b x hx.le) b (bernoulliParameter x)|≤1 := by
      simpa only [tiltedRecord_mean] using hm
    have hh := mul_le_mul_of_nonneg_right (h.2 hm') hzn.le
    have he : ((((countPolynomial01 b)^n).coeff m:ℝ)*x^m/(partition01 b x)^n*
        Real.sqrt (n:ℝ))*(partition01 b x)^n=
        (((countPolynomial01 b)^n).coeff m:ℝ)*x^m*Real.sqrt (n:ℝ) := by field_simp
    rwa [he] at hh

end HoffmanChromatic
