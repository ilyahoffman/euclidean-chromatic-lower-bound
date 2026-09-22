import HoffmanChromatic.WeightedCoefficient

/-! Cancellation of the common square-root factor in the chromatic quotient. -/
namespace HoffmanChromatic

theorem coefficient_ratio_cancel (u v k A E c C t s : ℝ) (n m D : ℕ)
    (hk : 0≤k) (hC : 0<C) (hE : 0<E) (ht : 0<t) (hs : 0<s) (hs1 : s<1)
    (hfinite : u≤k*v)
    (hlower : c*A^n≤u*t^m*Real.sqrt (n:ℝ))
    (hupper : v*s^D*Real.sqrt (n:ℝ)≤C*E^n/(1-s)^2) :
    (c/C)*(1-s)^2*(s^D/t^m)*(A/E)^n≤k := by
  have hsq : 0<(1-s)^2 := sq_pos_of_pos (sub_pos.2 hs1)
  have hh := (le_div_iff₀ hsq).mp hupper
  have h1 := mul_le_mul_of_nonneg_right hlower (mul_nonneg (pow_pos hs D).le hsq.le)
  have h2 := mul_le_mul_of_nonneg_right hfinite
    (mul_nonneg (mul_nonneg (pow_pos ht m).le (Real.sqrt_nonneg (n:ℝ)))
      (mul_nonneg (pow_pos hs D).le hsq.le))
  have h3 := mul_le_mul_of_nonneg_left hh (mul_nonneg hk (pow_pos ht m).le)
  have hmain : c*A^n*s^D*(1-s)^2≤k*(C*E^n*t^m) := by
    nlinarith only [h1,h2,h3]
  have hden : 0<C*E^n*t^m := by positivity
  have he : (c/C)*(1-s)^2*(s^D/t^m)*(A/E)^n=
      (c*A^n*s^D*(1-s)^2)/(C*E^n*t^m) := by
    rw [div_pow]
    field_simp
    ring
  rw [he]
  exact (div_le_iff₀ hden).2 hmain

/-- A finite chromatic inequality and two coefficient estimates give a
uniform parameter bound. No asymptotic estimate is left as a hypothesis. -/
theorem uniform_polynomial_chromatic_bound {J K : Type*} [Fintype J] [Fintype K]
    (b : J → ℕ) (e : K → ℕ) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1)
    (hfinite : ∀ n ell k : ℕ, (unitDistanceGraph n).Colorable k →
      ((countPolynomial01 b)^n).coeff (2*2^ell-1)≤
        k*weightedCount (countPolynomial01 e) n (2^ell-1)) :
    ∃ q : ℝ, 0<q ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀≤n → ∀ ell : ℕ, ∀ t s : ℝ,
    ε≤t → t≤1 → ε≤s → s<1 →
    |((2*2^ell-1:ℕ):ℝ)-(n:ℝ)*mean01 b t|≤1 →
    ChromaticLowerBound n
      (q*(1-s)^2*(s^(2^ell-1)/t^(2*2^ell-1))*(partition01 b t/partition01 e s)^n) := by
  obtain ⟨c,C₁,hc,hC₁,N₁,hlo⟩ := uniform_coefficient_bounds b ε hε hε1
  obtain ⟨C,hC,N₂,hup⟩ := uniform_weighted_coefficient_bound e ε hε hε1
  refine ⟨c/C,div_pos hc hC,max N₁ N₂,?_⟩
  intro n hn ell t s hεt ht1 hεs hs1 hmean k hk
  have ht : 0<t := hε.trans_le hεt
  have hs : 0<s := hε.trans_le hεs
  have hfiniteR : (((countPolynomial01 b)^n).coeff (2*2^ell-1):ℝ)≤
      (k:ℝ)*(weightedCount (countPolynomial01 e) n (2^ell-1):ℝ) := by
    exact_mod_cast hfinite n ell k hk
  exact coefficient_ratio_cancel _ _ _ _ _ _ _ _ _ n (2*2^ell-1) (2^ell-1)
    (Nat.cast_nonneg k) hC (partition01_pos e s hs.le) ht hs hs1 hfiniteR
    ((hlo n (by omega) t hεt ht1 (2*2^ell-1)).2 hmean)
    (hup n (by omega) s hεs hs1 (2^ell-1))

end HoffmanChromatic
