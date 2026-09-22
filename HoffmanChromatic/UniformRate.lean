import HoffmanChromatic.SharpParameters
import HoffmanChromatic.SaddlePoint

/-! Uniform exponential rate bounds, including a constant independent of n. -/
namespace HoffmanChromatic

theorem parameter_rate_identity (A E t s : ℝ) (hA : 0<A) (hE : 0<E)
    (ht : 0<t) (hs : 0<s) (n P : ℕ) (hn : 0<n) (hP : 0<P) :
    (s^(P-1)/t^(2*P-1))*(A/E)^n=(t/s)*Real.exp ((n:ℝ)*
      (Real.log A-2*((P:ℝ)/(n:ℝ))*Real.log t-Real.log E+((P:ℝ)/(n:ℝ))*Real.log s)) := by
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hleft : 0<(s^(P-1)/t^(2*P-1))*(A/E)^n := by positivity
  have hlog : Real.log ((s^(P-1)/t^(2*P-1))*(A/E)^n)=Real.log (t/s)+(n:ℝ)*
      (Real.log A-2*((P:ℝ)/(n:ℝ))*Real.log t-Real.log E+((P:ℝ)/(n:ℝ))*Real.log s) := by
    rw [Real.log_mul (by positivity) (by positivity),Real.log_div (by positivity) (by positivity),
      Real.log_pow,Real.log_pow,Real.log_pow,Real.log_div hA.ne' hE.ne',Real.log_div ht.ne' hs.ne']
    rw [Nat.cast_sub (by omega : 1≤P),Nat.cast_sub (by omega : 1≤2*P)]
    push_cast
    field_simp
    ring
  rw [← Real.exp_log hleft,hlog,Real.exp_add,Real.exp_log (div_pos ht hs)]

theorem uniform_rate_from_brackets {J K : Type*} [Fintype J] [Fintype K]
    (b : J → ℕ) (e : K → ℕ)
    (hbL : mean01 b (1/4)<2*(37/100)) (hbU : 2*(3/4)<mean01 b (4/5))
    (heL : mean01 e (1/4)<37/100) (heU : 3/4<mean01 e (4/5))
    (hfinite : ∀ n ell k : ℕ, (unitDistanceGraph n).Colorable k →
      ((countPolynomial01 b)^n).coeff (2*2^ell-1)≤
        k*weightedCount (countPolynomial01 e) n (2^ell-1)) :
    ∃ c : ℝ, 0<c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀≤n → ∀ ell : ℕ,
    (37/100:ℝ)≤(2^ell:ℕ)/(n:ℝ) → (2^ell:ℕ)/(n:ℝ)≤3/4 →
    ChromaticLowerBound n (c*Real.exp ((n:ℝ)*
      (logarithmicRate (partition01 b) (2*((2^ell:ℕ)/(n:ℝ)))-
       logarithmicRate (partition01 e) ((2^ell:ℕ)/(n:ℝ))))) := by
  obtain ⟨q,hq,N,hparam⟩ := uniform_polynomial_chromatic_bound b e (1/5) (by norm_num) (by norm_num) hfinite
  refine ⟨q/125,by positivity,max 1 N,?_⟩
  intro n hn ell hδL hδU
  have hn1 : 1≤n := by omega
  have hn0 : 0<n := by omega
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn0)
  let δ : ℝ := (2^ell:ℕ)/(n:ℝ)
  change (37/100:ℝ)≤δ at hδL
  change δ≤3/4 at hδU
  obtain ⟨t,htL,htU,hmt,htu⟩ := saddle_exists_unique b (1/4) (4/5) (2*δ)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
  obtain ⟨s,hsL,hsU,hms,hsu⟩ := saddle_exists_unique e (1/4) (4/5) δ
    (by norm_num) (by norm_num) (by linarith) (by linarith)
  have ht : 0<t := by linarith
  have ht1 : t<1 := by linarith
  have hs : 0<s := by linarith
  have hs1 : s<1 := by linarith
  have hP : 0<2^ell := by positivity
  have hmean : |((2*2^ell-1:ℕ):ℝ)-(n:ℝ)*mean01 b t|≤1 := by
    rw [hmt,Nat.cast_sub (by omega : 1≤2*2^ell)]
    have he : (n:ℝ)*(2*δ)=2*(2^ell:ℕ) := by dsimp [δ]; field_simp
    rw [he]
    push_cast
    norm_num
  have hp := hparam n (by omega) ell t s (by linarith) ht1.le (by linarith) hs1 hmean
  have hR : logarithmicRate (partition01 b) (2*δ)-logarithmicRate (partition01 e) δ=
      Real.log (partition01 b t)-2*δ*Real.log t-Real.log (partition01 e s)+δ*Real.log s := by
    rw [logarithmicRate_at_saddle b t (2*δ) ht ht1 hmt,
      logarithmicRate_at_saddle e s δ hs hs1 hms]
    ring
  have hid := parameter_rate_identity (partition01 b t) (partition01 e s) t s
    (partition01_pos b t ht.le) (partition01_pos e s hs.le) ht hs n (2^ell) hn0 hP
  have hfactor : (1/125:ℝ)≤(1-s)^2*(t/s) := by
    have hsq : (1/25:ℝ)≤(1-s)^2 := by nlinarith only [hsU]
    have hts : (1/5:ℝ)≤t/s := by
      apply (le_div_iff₀ hs).2
      linarith
    have hh := mul_le_mul hsq hts (by norm_num) (sq_nonneg (1-s))
    norm_num at hh
    exact hh
  intro k hk
  have hh := hp k hk
  change q*(1-s)^2*(s^(2^ell-1)/t^(2*2^ell-1))*(partition01 b t/partition01 e s)^n≤(k:ℝ) at hh
  have hrewrite : q*(1-s)^2*(s^(2^ell-1)/t^(2*2^ell-1))*(partition01 b t/partition01 e s)^n=
      q*((1-s)^2*(t/s))*Real.exp ((n:ℝ)*
        (logarithmicRate (partition01 b) (2*δ)-logarithmicRate (partition01 e) δ)) := by
    rw [hR]
    dsimp [δ]
    calc
      _ = q*(1-s)^2*((s^(2^ell-1)/t^(2*2^ell-1))*(partition01 b t/partition01 e s)^n) := by ring
      _ = _ := by rw [hid]; ring
  rw [hrewrite] at hh
  have hfac := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor hq.le)
    (Real.exp_pos ((n:ℝ)*(logarithmicRate (partition01 b) (2*δ)-logarithmicRate (partition01 e) δ))).le
  change q/125*Real.exp ((n:ℝ)*(logarithmicRate (partition01 b) (2*δ)-logarithmicRate (partition01 e) δ))≤(k:ℝ)
  nlinarith only [hh,hfac]

theorem six_uniform_rate :
    ∃ c : ℝ, 0<c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀≤n → ∀ ell : ℕ,
    (37/100:ℝ)≤(2^ell:ℕ)/(n:ℝ) → (2^ell:ℕ)/(n:ℝ)≤3/4 →
    ChromaticLowerBound n (c*Real.exp ((n:ℝ)*delta6 ((2^ell:ℕ)/(n:ℝ)))) := by
  have hbL : mean01 tailA6 (1/4)<2*(37/100) := by
    norm_num [mean01,partition01,tailA6,Fin.sum_univ_succ]
  have hbU : 2*(3/4)<mean01 tailA6 (4/5) := by
    norm_num [mean01,partition01,tailA6,Fin.sum_univ_succ]
  have heL : mean01 tailE6 (1/4)<37/100 := by
    norm_num [mean01,partition01,tailE6,Fin.sum_univ_succ]
  have heU : 3/4<mean01 tailE6 (4/5) := by
    norm_num [mean01,partition01,tailE6,Fin.sum_univ_succ]
  have hf : ∀ n ell k : ℕ, (unitDistanceGraph n).Colorable k →
      ((countPolynomial01 tailA6)^n).coeff (2*2^ell-1)≤
        k*weightedCount (countPolynomial01 tailE6) n (2^ell-1) := by
    simpa only [count01_A6,count01_E6] using finite_six
  have hA : partition01 tailA6=realA6 := funext partition01_A6
  have hE : partition01 tailE6=realE6 := funext partition01_E6
  simpa only [hA,hE,delta6] using uniform_rate_from_brackets tailA6 tailE6 hbL hbU heL heU hf

theorem seven_uniform_rate :
    ∃ c : ℝ, 0<c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀≤n → ∀ ell : ℕ,
    (37/100:ℝ)≤(2^ell:ℕ)/(n:ℝ) → (2^ell:ℕ)/(n:ℝ)≤3/4 →
    ChromaticLowerBound n (c*Real.exp ((n:ℝ)*delta7 ((2^ell:ℕ)/(n:ℝ)))) := by
  have hbL : mean01 tailA7 (1/4)<2*(37/100) := by
    norm_num [mean01,partition01,tailA7,Fin.sum_univ_succ]
  have hbU : 2*(3/4)<mean01 tailA7 (4/5) := by
    norm_num [mean01,partition01,tailA7,Fin.sum_univ_succ]
  have heL : mean01 tailE7 (1/4)<37/100 := by
    norm_num [mean01,partition01,tailE7,Fin.sum_univ_succ]
  have heU : 3/4<mean01 tailE7 (4/5) := by
    norm_num [mean01,partition01,tailE7,Fin.sum_univ_succ]
  have hf : ∀ n ell k : ℕ, (unitDistanceGraph n).Colorable k →
      ((countPolynomial01 tailA7)^n).coeff (2*2^ell-1)≤
        k*weightedCount (countPolynomial01 tailE7) n (2^ell-1) := by
    simpa only [count01_A7,count01_E7] using finite_seven
  have hA : partition01 tailA7=realA7 := funext partition01_A7
  have hE : partition01 tailE7=realE7 := funext partition01_E7
  simpa only [hA,hE,delta7] using uniform_rate_from_brackets tailA7 tailE7 hbL hbU heL heU hf

end HoffmanChromatic
