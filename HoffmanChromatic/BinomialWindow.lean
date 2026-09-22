import HoffmanChromatic.BinomialEntropy

/-! Uniform inverse-square-root bounds in a binomial central window. -/
namespace HoffmanChromatic

/-- Uniform constants when both the success probability and empirical frequency
stay away from the endpoints. The central-window hypothesis controls divergence. -/
theorem binomial_window_bounds (a A : ℝ) (ha : 0<a) (_hA : 0≤A) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ n k : ℕ, 0<k → k<n → ∀ t : ℝ,
      a≤t → t≤1-a → a≤(k:ℝ)/(n:ℝ) → (k:ℝ)/(n:ℝ)≤1-a →
      |(k:ℝ)-(n:ℝ)*t| ≤ A*Real.sqrt (n:ℝ) →
      c ≤ binomialMass n k t*Real.sqrt (n:ℝ) ∧
      binomialMass n k t*Real.sqrt (n:ℝ) ≤ C := by
  obtain ⟨B, hB, hb⟩ := binomial_log_error_bounded
  refine ⟨Real.exp (-A^2/a^2-B), Real.exp (B-Real.log a), Real.exp_pos _, Real.exp_pos _, ?_⟩
  intro n k hk hkn t hat hta hau hua hwin
  have hn : (0:ℝ)<n := by exact_mod_cast (lt_trans hk hkn)
  have ht : 0<t := ha.trans_le hat
  have ht1 : t<1 := by linarith
  have hu : 0<(k:ℝ)/(n:ℝ) := ha.trans_le hau
  have hu1 : (k:ℝ)/(n:ℝ)<1 := by linarith
  have hv : 0<1-(k:ℝ)/(n:ℝ) := by linarith
  have htden : a^2 ≤ t*(1-t) := by nlinarith only [mul_le_mul hat (show a≤1-t by linarith) ha.le ht.le]
  have huden : a^2 ≤ ((k:ℝ)/(n:ℝ))*(1-(k:ℝ)/(n:ℝ)) := by
    nlinarith only [mul_le_mul hau (show a≤1-(k:ℝ)/(n:ℝ) by linarith) ha.le hu.le]
  have huid : ((k:ℝ)/(n:ℝ))*(1-(k:ℝ)/(n:ℝ)) ≤ 1 := by
    nlinarith only [hu.le, hu1.le, sq_nonneg ((k:ℝ)/(n:ℝ))]
  have hsq := mul_self_le_mul_self (abs_nonneg _) hwin
  have hsq' : ((k:ℝ)-(n:ℝ)*t)^2 ≤ A^2*(n:ℝ) := by
    simpa only [← sq, mul_pow, sq_abs, Real.sq_sqrt hn.le] using hsq
  have hratio : (n:ℝ)*((k:ℝ)/(n:ℝ)-t)^2 ≤ A^2 := by
    have hid : (n:ℝ)*((k:ℝ)/(n:ℝ)-t)^2 = ((k:ℝ)-(n:ℝ)*t)^2/(n:ℝ) := by field_simp; ring
    rw [hid]
    exact (div_le_iff₀ hn).2 hsq'
  have hDlo := bernoulliDivergence_nonneg ((k:ℝ)/(n:ℝ)) t hu hu1 ht ht1
  have hDhi := bernoulliDivergence_upper ((k:ℝ)/(n:ℝ)) t hu hu1 ht ht1
  have hdenpos : 0<a^2 := sq_pos_of_pos ha
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg ((k:ℝ)/(n:ℝ)-t)) hdenpos htden
  have hDhi' : (n:ℝ)*bernoulliDivergence ((k:ℝ)/(n:ℝ)) t ≤ A^2/a^2 := by
    calc
      _ ≤ (n:ℝ)*(((k:ℝ)/(n:ℝ)-t)^2/a^2) :=
        mul_le_mul_of_nonneg_left (hDhi.trans hdiv) hn.le
      _ = ((n:ℝ)*((k:ℝ)/(n:ℝ)-t)^2)/a^2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hratio hdenpos.le
  have hDlo' := mul_nonneg hn.le hDlo
  have hloglo := Real.log_le_log hdenpos huden
  rw [Real.log_pow] at hloglo
  have hloghi := Real.log_nonpos (mul_pos hu hv).le huid
  have he := hb n k hk hkn t ht ht1
  dsimp only at he
  have hfac : Real.log ((n:ℝ)*((k:ℝ)/(n:ℝ))*(1-(k:ℝ)/(n:ℝ))) =
      Real.log (n:ℝ)+Real.log (((k:ℝ)/(n:ℝ))*(1-(k:ℝ)/(n:ℝ))) := by
    rw [mul_assoc, Real.log_mul hn.ne' (mul_ne_zero hu.ne' hv.ne')]
  rw [hfac] at he
  have hlower := (abs_le.mp he).1
  have hupper := (abs_le.mp he).2
  have hmass := binomialMass_pos hkn.le ht ht1
  have hnorm : 0<binomialMass n k t*Real.sqrt (n:ℝ) := mul_pos hmass (Real.sqrt_pos.2 hn)
  have hlog : Real.log (binomialMass n k t*Real.sqrt (n:ℝ)) =
      Real.log (binomialMass n k t)+(1/2:ℝ)*Real.log (n:ℝ) := by
    rw [Real.log_mul hmass.ne' (Real.sqrt_pos.2 hn).ne', Real.log_sqrt hn.le]
    ring
  constructor
  · apply (Real.le_log_iff_exp_le hnorm).mp
    rw [hlog]
    simp only [neg_div]
    nlinarith only [hlower, hDhi', hloghi]
  · apply (Real.log_le_iff_le_exp hnorm).mp
    rw [hlog]
    norm_num only [Nat.cast_ofNat] at hloglo
    nlinarith only [hupper, hDlo', hloglo]

/-- The empirical-frequency side conditions follow uniformly for large sample size. -/
theorem binomial_central_bounds (a A : ℝ) (ha : 0<a) (hA : 0≤A) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ k : ℕ, ∀ t : ℝ,
      a≤t → t≤1-a → |(k:ℝ)-(n:ℝ)*t|≤A*Real.sqrt (n:ℝ) →
      c ≤ binomialMass n k t*Real.sqrt (n:ℝ) ∧
      binomialMass n k t*Real.sqrt (n:ℝ) ≤ C := by
  obtain ⟨c, C, hc, hC, hb⟩ := binomial_window_bounds (a/2) A (by linarith) hA
  obtain ⟨N, hN⟩ := exists_nat_ge (4*A^2/a^2+1)
  refine ⟨c, C, hc, hC, N, ?_⟩
  intro n hn k t hat hta hwin
  have hncast : (N:ℝ)≤n := by exact_mod_cast hn
  have hNdiv : 4*A^2/a^2≤(n:ℝ)-1 := by linarith
  have ha2 : 0<a^2 := sq_pos_of_pos ha
  have hnR : (0:ℝ)<n := by
    have hp : 0≤4*A^2/a^2 := by positivity
    linarith
  have hlarge : 4*A^2 ≤ (n:ℝ)*a^2 := by
    have hh := (div_le_iff₀ ha2).mp (show 4*A^2/a^2≤(n:ℝ) by linarith)
    exact hh
  have hs := mul_self_le_mul_self (abs_nonneg _) hwin
  have hs' : ((k:ℝ)-(n:ℝ)*t)^2≤A^2*(n:ℝ) := by
    simpa only [← sq, mul_pow, sq_abs, Real.sq_sqrt hnR.le] using hs
  have hratio : (n:ℝ)*((k:ℝ)/(n:ℝ)-t)^2≤A^2 := by
    have hi : (n:ℝ)*((k:ℝ)/(n:ℝ)-t)^2=((k:ℝ)-(n:ℝ)*t)^2/(n:ℝ) := by field_simp; ring
    rw [hi]
    exact (div_le_iff₀ hnR).2 hs'
  have hsq : ((k:ℝ)/(n:ℝ)-t)^2≤(a/2)^2 := by
    apply (mul_le_mul_left hnR).mp
    nlinarith only [hratio, hlarge]
  have habs : |(k:ℝ)/(n:ℝ)-t|≤a/2 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by linarith : 0≤a/2)).mp
    simpa only [sq_abs] using hsq
  have hu : a/2≤(k:ℝ)/(n:ℝ) := by linarith [(abs_le.mp habs).1]
  have hu1 : (k:ℝ)/(n:ℝ)≤1-a/2 := by linarith [(abs_le.mp habs).2]
  have hkR : (0:ℝ)<k := (div_pos_iff_of_pos_right hnR).mp (show 0<(k:ℝ)/(n:ℝ) by linarith)
  have hknR : (k:ℝ)<n := (div_lt_one hnR).mp (show (k:ℝ)/(n:ℝ)<1 by linarith)
  apply hb n k (by exact_mod_cast hkR) (by exact_mod_cast hknR) t
    (by linarith) (by linarith) hu hu1 hwin

end HoffmanChromatic
