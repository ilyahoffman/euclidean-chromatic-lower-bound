import HoffmanChromatic.FiniteLaw
import HoffmanChromatic.BinomialPolynomial

/-! Uniform upper estimates for finite mixtures of binomial laws. -/
namespace HoffmanChromatic

universe u

variable {Ω : Type*} [Fintype Ω]

noncomputable def binomialMixture (p : FiniteLaw Ω) (N R : Ω → ℕ) (m : ℕ) (t : ℝ) : ℝ :=
  p.mean (fun x => binomialMassZ (N x) ((m:ℤ)-R x) t)

theorem sqrt_size_comparison (a x y : ℝ) (ha : 0<a) (h : a*x/2≤y) :
    Real.sqrt x≤Real.sqrt (2/a)*Real.sqrt y := by
  have hh : x≤(2/a)*y := by
    have hi : (2/a)*y=(2*y)/a := by ring
    rw [hi]
    apply (le_div_iff₀ ha).2
    nlinarith only [h]
  have hs := Real.sqrt_le_sqrt hh
  rwa [Real.sqrt_mul (by positivity : 0≤2/a)] at hs

theorem small_count_mass (p : FiniteLaw Ω) (N : Ω → ℕ) (n : ℕ)
    (a α : ℝ) (ha : 0<a) (hα : a≤α) (hn : 0<n)
    (hv : p.mean (fun x => ((N x:ℝ)-(n:ℝ)*α)^2)≤(n:ℝ)) :
    p.mass (fun x => (N x:ℝ)<a*(n:ℝ)/2)*(a^2*(n:ℝ))≤4 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have h := p.chebyshev_event (fun x => (N x:ℝ)) ((n:ℝ)*α) (a*(n:ℝ)/2)
    (by positivity) (fun x => (N x:ℝ)<a*(n:ℝ)/2) (by
      intro x hx
      have hh := mul_le_mul_of_nonneg_left hα hnR.le
      have habs := le_abs_self ((n:ℝ)*α-(N x:ℝ))
      rw [abs_sub_comm] at habs
      linarith)
  have hh := h.trans hv
  apply (mul_le_mul_left hnR).mp
  nlinarith only [hh]

theorem small_count_scaled (p : FiniteLaw Ω) (N : Ω → ℕ) (n : ℕ)
    (a α : ℝ) (ha : 0<a) (hα : a≤α) (hn : 1≤n)
    (hv : p.mean (fun x => ((N x:ℝ)-(n:ℝ)*α)^2)≤(n:ℝ)) :
    p.mass (fun x => (N x:ℝ)<a*(n:ℝ)/2)*Real.sqrt (n:ℝ)≤4/a^2 := by
  have hh := small_count_mass p N n a α ha hα (by omega) hv
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hs : Real.sqrt (n:ℝ)≤(n:ℝ) := by
    have hsq := Real.sq_sqrt (show (0:ℝ)≤n by positivity)
    have hp := Real.sqrt_nonneg (n:ℝ)
    nlinarith only [hsq, hp, hnR]
  have hmul := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (p.mass_nonneg (fun x => (N x:ℝ)<a*(n:ℝ)/2)) (sq_nonneg a))
  apply (le_div_iff₀ (sq_pos_of_pos ha)).2
  nlinarith only [hmul, hh]

theorem binomial_mixture_uniform_upper (a : ℝ) (ha : 0<a) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀≤n →
    ∀ (Ω : Type u) [Fintype Ω],
    ∀ (p : FiniteLaw Ω) (N R : Ω → ℕ) (α t : ℝ), a≤α → a≤t → t≤1-a →
    p.mean (fun x => ((N x:ℝ)-(n:ℝ)*α)^2)≤(n:ℝ) →
    ∀ m : ℕ, binomialMixture p N R m t*Real.sqrt (n:ℝ)≤C := by
  obtain ⟨C,hC,K,hK⟩ := binomial_uniform_upper a ha
  let L := Real.sqrt (2/a)
  have hL : 0<L := Real.sqrt_pos.2 (by positivity)
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (max 1 (2*(K:ℝ)/a))
  refine ⟨4/a^2+L*C, by positivity, n₀, ?_⟩
  intro n hn Ω inst p N R α t hα hat hta hv m
  have hncast : (n₀:ℝ)≤n := by exact_mod_cast hn
  have hn1R : (1:ℝ)≤n := (le_max_left _ _).trans (hn₀.trans hncast)
  have hn1 : 1≤n := by exact_mod_cast hn1R
  have hnK : (K:ℝ)≤a*(n:ℝ)/2 := by
    have hh : 2*(K:ℝ)/a≤(n:ℝ) := (le_max_right _ _).trans (hn₀.trans hncast)
    have hx := (div_le_iff₀ ha).mp hh
    nlinarith only [hx]
  have ht : 0<t := ha.trans_le hat
  have ht1 : t<1 := by linarith
  let S : Ω → Prop := fun x => (N x:ℝ)<a*(n:ℝ)/2
  let f : Ω → ℝ := fun x => binomialMassZ (N x) ((m:ℤ)-R x) t*Real.sqrt (n:ℝ)
  have hbad : ∀ x, S x → f x≤Real.sqrt (n:ℝ) := by
    intro x _
    exact (mul_le_mul_of_nonneg_right (binomialMassZ_le_one _ _ ht.le ht1.le) (Real.sqrt_nonneg _)).trans_eq (one_mul _)
  have hgood : ∀ x, ¬S x → f x≤L*C := by
    intro x hx
    have hNx : a*(n:ℝ)/2≤(N x:ℝ) := le_of_not_gt hx
    have hNK : K≤N x := by exact_mod_cast hnK.trans hNx
    have hu : binomialMassZ (N x) ((m:ℤ)-R x) t*Real.sqrt (N x:ℝ)≤C := by
      unfold binomialMassZ
      split_ifs
      · exact hK (N x) hNK _ t hat hta
      · simpa using hC.le
    have hs := sqrt_size_comparison a (n:ℝ) (N x:ℝ) ha hNx
    have hh := mul_le_mul_of_nonneg_left hs (binomialMassZ_nonneg (N x) ((m:ℤ)-R x) ht.le ht1.le)
    have hh' := mul_le_mul_of_nonneg_left hu hL.le
    dsimp [f, L] at *
    nlinarith only [hh, hh']
  have hm := p.mean_split_upper S f (Real.sqrt (n:ℝ)) (L*C) hbad hgood
  have hsmall := small_count_scaled p N n a α ha hα hn1 hv
  have hnonneg := p.mass_nonneg S
  have hcost : 0≤L*C*p.mass S := mul_nonneg (mul_pos hL hC).le hnonneg
  have hmean : p.mean f=binomialMixture p N R m t*Real.sqrt (n:ℝ) := by
    exact p.mean_mul_const _ _
  rw [hmean] at hm
  change p.mass S*Real.sqrt (n:ℝ)≤4/a^2 at hsmall
  nlinarith only [hm, hsmall, hcost]

end HoffmanChromatic
