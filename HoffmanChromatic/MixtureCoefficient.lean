import HoffmanChromatic.MixturePolynomial
import HoffmanChromatic.MixtureLower

/-! A local coefficient estimate, uniform over a family of finite laws. -/
namespace HoffmanChromatic

universe u

theorem mixture_coefficient_bounds (a B : ℝ) (ha : 0<a) (hB : 1≤B) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀≤n →
    ∀ (A : Type u) [Fintype A] (b : A → ℕ) (p : FiniteLaw (Option A)) (t : ℝ),
    (∀ j, (b j:ℝ)≤B) → a≤p.weight none → a≤t → t≤1-a → ∀ m : ℕ,
    ((mixturePolynomial p b t)^n).coeff m*Real.sqrt (n:ℝ)≤C ∧
    (|(m:ℝ)-(n:ℝ)*recordMean p b t|≤1 →
      c≤((mixturePolynomial p b t)^n).coeff m*Real.sqrt (n:ℝ)) := by
  obtain ⟨c,hc,N₁,hlo⟩ := binomial_mixture_uniform_lower.{u} a B ha hB
  obtain ⟨C,hC,N₂,hup⟩ := binomial_mixture_uniform_upper.{u} a ha
  refine ⟨c,C,hc,hC,max N₁ N₂,?_⟩
  intro n hn A inst b p t hb hα hat hta m
  have ht : 0≤t := (ha.trans_le hat).le
  have ht1 : t≤1 := by linarith
  have he : ((mixturePolynomial p b t)^n).coeff m=
      binomialMixture (p.iid n) recordN (recordR b) m t := mixturePolynomial_coeff p b t n m
  rw [he]
  constructor
  · exact hup n (by omega) (Fin n → Option A) (p.iid n) recordN (recordR b)
      (p.weight none) t hα hat hta (recordN_variance p n) m
  · intro hm
    exact hlo n (by omega) (Fin n → Option A) (p.iid n) recordN (recordR b)
      (p.weight none) (recordMean p b t) t hα hat hta (recordN_le n)
      (recordN_variance p n) (recordW_mean p b t n)
      (recordW_variance p b t B ht ht1 hB hb n) m hm

end HoffmanChromatic
