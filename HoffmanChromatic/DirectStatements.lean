import HoffmanChromatic.Results
import HoffmanChromatic.Uniform

/-!
An independent consumer-side audit of the delivered project.
The endpoint statements below use arbitrary colouring functions and the
Euclidean distance directly, not the project's ChromaticLowerBound alias.
The two rates are restated with the four explicit polynomials.
-/

namespace HoffmanChromatic.Direct

noncomputable def rate6 (d : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ t : ℝ, 0 < t ∧ t < 1 ∧
    v = Real.log (1 + t + t^3 + t^6 + t^10 + t^15) - (2*d)*Real.log t} -
  sInf {v : ℝ | ∃ s : ℝ, 0 < s ∧ s < 1 ∧
    v = Real.log (1 + s + s^3 + s^4 + s^8 + s^9) - d*Real.log s}

noncomputable def rate7 (d : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ t : ℝ, 0 < t ∧ t < 1 ∧
    v = Real.log (1 + t + t^3 + t^6 + t^10 + t^15 + t^21) - (2*d)*Real.log t} -
  sInf {v : ℝ | ∃ s : ℝ, 0 < s ∧ s < 1 ∧
    v = Real.log (1 + s + s^3 + s^4 + s^8 + s^9 + s^11) - d*Real.log s}

theorem direct_colouring_bound (d k : ℕ) (b : ℝ)
    (h : HoffmanChromatic.ChromaticLowerBound d b)
    (f : EuclideanSpace ℝ (Fin d) → Fin k)
    (hf : ∀ x y, dist x y = 1 → f x ≠ f y) : b ≤ (k : ℝ) := by
  apply h k
  exact ⟨SimpleGraph.Coloring.mk f (fun {x y} hxy => hf x y hxy)⟩

theorem direct_rounded :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ k : ℕ,
    ∀ f : EuclideanSpace ℝ (Fin d) → Fin k,
    (∀ x y, dist x y = 1 → f x ≠ f y) → ((13 : ℝ)/10)^d ≤ (k : ℝ) := by
  obtain ⟨d₀, h⟩ := HoffmanChromatic.rounded_chromatic
  exact ⟨d₀, fun d hd k f hf => direct_colouring_bound d k _ (h d hd) f hf⟩

theorem direct_subsequence :
    ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧ ∀ k : ℕ,
    ∀ f : EuclideanSpace ℝ (Fin d) → Fin k,
    (∀ x y, dist x y = 1 → f x ≠ f y) → ((329 : ℝ)/250)^d ≤ (k : ℝ) := by
  intro N
  obtain ⟨d, hd, h⟩ := HoffmanChromatic.subsequence_chromatic N
  exact ⟨d, hd, fun k f hf => direct_colouring_bound d k _ h f hf⟩

theorem direct_uniform :
    ∃ a : ℝ, (371979 : ℝ)/1000000 < a ∧ a < (371980 : ℝ)/1000000 ∧
    rate6 a = rate7 (2*a) ∧
    (∀ b : ℝ, (371979 : ℝ)/1000000 < b → b < (371980 : ℝ)/1000000 →
      rate6 b = rate7 (2*b) → b = a) ∧
    (1309251 : ℝ)/1000000 < Real.exp (rate6 a) ∧
    Real.exp (rate6 a) < (1309252 : ℝ)/1000000 ∧
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ k : ℕ,
    ∀ f : EuclideanSpace ℝ (Fin d) → Fin k,
    (∀ x y, dist x y = 1 → f x ≠ f y) → c*(Real.exp (rate6 a))^d ≤ (k : ℝ) := by
  obtain ⟨a, ha, hu, hL, hU, c, hc, d₀, h⟩ := HoffmanChromatic.uniform_chromatic
  refine ⟨a, ha.1, ha.2.1, ha.2.2, ?_, hL, hU, c, hc, d₀, ?_⟩
  · intro b hbL hbU hb
    exact hu b ⟨hbL, hbU, hb⟩
  · intro d hd k f hf
    exact direct_colouring_bound d k _ (h d hd) f hf

end HoffmanChromatic.Direct
