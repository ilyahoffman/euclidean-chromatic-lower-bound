import HoffmanChromatic.Rounded

/-! Closed endpoint statements with their quantifiers displayed explicitly.
The sharp constant-prefactor endpoint is proved separately in `Uniform.lean`.
-/
namespace HoffmanChromatic

theorem rounded_euclidean_chromatic :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ k : ℕ,
      (unitDistanceGraph d).Colorable k → ((13:ℝ)/10)^d ≤ (k:ℝ) :=
  rounded_chromatic

theorem subsequence_euclidean_chromatic :
    ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧ ∀ k : ℕ,
      (unitDistanceGraph d).Colorable k → ((329:ℝ)/250)^d ≤ (k:ℝ) :=
  subsequence_chromatic

end HoffmanChromatic
