import HoffmanChromatic.MixtureUpper

/-! Uniform lower bounds for binomial mixtures near their mean. -/
namespace HoffmanChromatic

universe u

/-- All constants precede the finite sample space: the space may vary with `n`. -/
theorem binomial_mixture_uniform_lower (a B : ℝ) (ha : 0<a) (hB : 1≤B) :
    ∃ c : ℝ, 0<c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀≤n →
    ∀ (Ω : Type u) [Fintype Ω], ∀ (p : FiniteLaw Ω) (N R : Ω → ℕ) (α μ t : ℝ),
    a≤α → a≤t → t≤1-a → (∀ x, N x≤n) →
    p.mean (fun x => ((N x:ℝ)-(n:ℝ)*α)^2)≤(n:ℝ) →
    p.mean (fun x => (R x:ℝ)+t*(N x:ℝ))=(n:ℝ)*μ →
    p.mean (fun x => ((R x:ℝ)+t*(N x:ℝ)-(n:ℝ)*μ)^2)≤(n:ℝ)*B^2 →
    ∀ m : ℕ, |(m:ℝ)-(n:ℝ)*μ|≤1 →
    c≤binomialMixture p N R m t*Real.sqrt (n:ℝ) := by
  let D := 2*Real.sqrt (B^2+1)
  let L := Real.sqrt (2/a)
  have hD : 0<D := by dsimp [D]; positivity
  have hL : 0<L := Real.sqrt_pos.2 (by positivity)
  have hDsq : D^2=4*(B^2+1) := by
    dsimp [D]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  obtain ⟨c,C,hc,hC,K,hK⟩ := binomial_central_bounds_Z a (D*L) ha (mul_pos hD hL).le
  obtain ⟨n₀,hn₀⟩ := exists_nat_ge (max 1 (max (16/a^2) (2*(K:ℝ)/a)))
  refine ⟨c/2, by positivity, n₀, ?_⟩
  intro n hn Ω inst p N R α μ t hα hat hta hN hvN hmW hvW m hm
  have hncast : (n₀:ℝ)≤n := by exact_mod_cast hn
  have hn1R : (1:ℝ)≤n := (le_max_left _ _).trans (hn₀.trans hncast)
  have hn1 : 1≤n := by exact_mod_cast hn1R
  have hnR : (0:ℝ)<n := by linarith
  have hlarge : 16≤a^2*(n:ℝ) := by
    have hh : 16/a^2≤(n:ℝ) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (hn₀.trans hncast))
    have hx := (div_le_iff₀ (sq_pos_of_pos ha)).mp hh
    nlinarith only [hx]
  have hnK : (K:ℝ)≤a*(n:ℝ)/2 := by
    have hh : 2*(K:ℝ)/a≤(n:ℝ) :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (hn₀.trans hncast))
    have hx := (div_le_iff₀ ha).mp hh
    nlinarith only [hx]
  have ht : 0<t := ha.trans_le hat
  have ht1 : t<1 := by linarith
  let W : Ω → ℝ := fun x => (R x:ℝ)+t*(N x:ℝ)
  let S : Ω → Prop := fun x => (N x:ℝ)<a*(n:ℝ)/2
  let T : Ω → Prop := fun x => D*Real.sqrt (n:ℝ) < |W x-(m:ℝ)|
  let G : Ω → Prop := fun x => ¬(S x ∨ T x)
  have hS : p.mass S≤1/4 := by
    have hh := small_count_mass p N n a α ha hα (by omega) hvN
    have hp := p.mass_nonneg S
    have hx := mul_le_mul_of_nonneg_left hlarge hp
    change p.mass S*(a^2*(n:ℝ))≤4 at hh
    nlinarith only [hh,hx]
  have hT : p.mass T≤1/4 := by
    have he := p.shifted_second_moment W (m:ℝ)
    change p.mean W=(n:ℝ)*μ at hmW
    rw [hmW] at he
    have hmsq : ((n:ℝ)*μ-(m:ℝ))^2≤1 := by
      have hx := mul_self_le_mul_self (abs_nonneg ((m:ℝ)-(n:ℝ)*μ)) hm
      rw [← sq, sq_abs] at hx
      nlinarith only [hx]
    have hcenter : p.mean (fun x => (W x-(m:ℝ))^2)≤(n:ℝ)*B^2+1 := by
      change p.mean (fun x => (W x-(n:ℝ)*μ)^2)≤(n:ℝ)*B^2 at hvW
      linarith only [he,hvW,hmsq]
    have hh := (p.chebyshev_event W (m:ℝ) (D*Real.sqrt (n:ℝ))
      (mul_nonneg hD.le (Real.sqrt_nonneg _)) T (fun _ hx => le_of_lt hx)).trans hcenter
    rw [mul_pow, Real.sq_sqrt hnR.le, hDsq] at hh
    have hp : 0<(B^2+1)*(n:ℝ) := by positivity
    apply (mul_le_mul_left hp).mp
    nlinarith only [hh,hn1R]
  have hG : 1/2≤p.mass G := by
    have hh := p.mass_union_le S T
    have he := p.mass_compl (fun x => S x ∨ T x)
    change p.mass G=1-p.mass (fun x => S x ∨ T x) at he
    linarith only [hh,he,hS,hT]
  let f : Ω → ℝ := fun x => binomialMassZ (N x) ((m:ℤ)-R x) t*Real.sqrt (n:ℝ)
  have hf : ∀ x, 0≤f x := fun x =>
    mul_nonneg (binomialMassZ_nonneg _ _ ht.le ht1.le) (Real.sqrt_nonneg _)
  have hgood : ∀ x, G x → c≤f x := by
    intro x hx
    have hNx : a*(n:ℝ)/2≤(N x:ℝ) := le_of_not_gt (fun h => hx (Or.inl h))
    have hNK : K≤N x := by exact_mod_cast hnK.trans hNx
    have hwin : |W x-(m:ℝ)|≤D*Real.sqrt (n:ℝ) := le_of_not_gt (fun h => hx (Or.inr h))
    have hs := sqrt_size_comparison a (n:ℝ) (N x:ℝ) ha hNx
    have hscale := mul_le_mul_of_nonneg_left hs hD.le
    have hindex : |(((m:ℤ)-R x:ℤ):ℝ)-(N x:ℝ)*t|=|W x-(m:ℝ)| := by
      push_cast
      have he : (m:ℝ)-(R x:ℝ)-(N x:ℝ)*t=-(W x-(m:ℝ)) := by dsimp [W]; ring
      rw [he, abs_neg]
    have hwindow : |(((m:ℤ)-R x:ℤ):ℝ)-(N x:ℝ)*t|≤(D*L)*Real.sqrt (N x:ℝ) := by
      rw [hindex]
      dsimp [L] at *
      nlinarith only [hwin,hscale]
    have hh := (hK (N x) hNK ((m:ℤ)-R x) t hat hta hwindow).1
    have hroot := Real.sqrt_le_sqrt (show (N x:ℝ)≤n by exact_mod_cast hN x)
    exact hh.trans (mul_le_mul_of_nonneg_left hroot (binomialMassZ_nonneg _ _ ht.le ht1.le))
  have hh := p.mean_event_lower G f c hf hgood
  have hmG := mul_le_mul_of_nonneg_left hG hc.le
  have he : p.mean f=binomialMixture p N R m t*Real.sqrt (n:ℝ) := p.mean_mul_const _ _
  rw [he] at hh
  linarith only [hh,hmG]

end HoffmanChromatic
