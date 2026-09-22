import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Exact endpoint specifications. These are propositions, NOT proved theorems.
In particular, defining them introduces no mathematical assumption.

The ambient metric is the Euclidean (L2) metric, not the sup metric on a
plain function type. Bounds quantify over every finite proper colouring,
so there is no conversion of an infinite chromatic number to a real number.
-/

namespace HoffmanChromatic

open scoped BigOperators

def unitDistanceGraph (d : ℕ) : SimpleGraph (EuclideanSpace ℝ (Fin d)) where
  Adj x y := dist x y = 1
  symm := by intro x y h; simpa [dist_comm] using h
  loopless := by intro x; simp

def ChromaticLowerBound (d : ℕ) (b : ℝ) : Prop :=
  ∀ k : ℕ, (unitDistanceGraph d).Colorable k → b ≤ (k : ℝ)

def realA6 (t : ℝ) : ℝ := 1 + t + t^3 + t^6 + t^10 + t^15
def realA7 (t : ℝ) : ℝ := realA6 t + t^21
def realE6 (s : ℝ) : ℝ := 1 + s + s^3 + s^4 + s^8 + s^9
def realE7 (s : ℝ) : ℝ := realE6 s + s^11

noncomputable def logarithmicRate (Z : ℝ → ℝ) (m : ℝ) : ℝ :=
  sInf {z : ℝ | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ z = Real.log (Z t) - m * Real.log t}

noncomputable def delta6 (δ : ℝ) : ℝ :=
  logarithmicRate realA6 (2*δ) - logarithmicRate realE6 δ
noncomputable def delta7 (δ : ℝ) : ℝ :=
  logarithmicRate realA7 (2*δ) - logarithmicRate realE7 δ

def Crossing (a : ℝ) : Prop :=
  (371979 : ℝ)/1000000 < a ∧ a < (371980 : ℝ)/1000000 ∧ delta6 a = delta7 (2*a)

def UniformTarget : Prop :=
  ∃ a : ℝ, Crossing a ∧ (∀ b : ℝ, Crossing b → b = a) ∧
    (1309251 : ℝ)/1000000 < Real.exp (delta6 a) ∧
    Real.exp (delta6 a) < (1309252 : ℝ)/1000000 ∧
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ChromaticLowerBound d (c * (Real.exp (delta6 a))^d)

def RoundedTarget : Prop :=
  ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ChromaticLowerBound d (((13 : ℝ)/10)^d)

def SubsequenceTarget : Prop :=
  ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧ ChromaticLowerBound d (((329 : ℝ)/250)^d)

end HoffmanChromatic
