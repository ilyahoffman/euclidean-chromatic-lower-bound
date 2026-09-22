import HoffmanChromatic.TypeChromatic
import Mathlib.Tactic.FinCases

/-!
The infinite-dimensional subsequence result, proved from the finite theorem.
Exact rational Gibbs weights give integer multiplicities after clearing one
denominator. Stirling supplies their exponential rate. A bounded number of
extra coordinates of value one gives a power-of-two layer exactly.
-/

namespace HoffmanChromatic

open scoped BigOperators

def gibbsCounts (i : Fin 7) : ℕ :=
  131^(sevenWeight i) * 200^(21-sevenWeight i)

theorem sevenWeight_values (i : Fin 7) :
    sevenWeight i = ![21, 10, 3, 0, 1, 6, 15] i := by
  fin_cases i <;> rfl

theorem gibbsCounts_scaled (i : Fin 7) :
    (gibbsCounts i : ℝ) = (200:ℝ)^21 * ((131:ℝ)/200)^(sevenWeight i) := by
  simp only [gibbsCounts, sevenWeight_values]
  fin_cases i <;> norm_num

theorem gibbsCounts_mass_pos : 0 < typeMass gibbsCounts := by
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  unfold gibbsCounts
  positivity

theorem gibbsCounts_energy_pos : 0 < typeEnergy gibbsCounts := by
  have h : 0 < sevenWeight (0 : Fin 7)*gibbsCounts 0 := by
    norm_num [sevenWeight, gibbsCounts, letterWeight, intervalLetter, tau]
  exact h.trans_le (Finset.single_le_sum
    (f := fun i : Fin 7 => sevenWeight i*gibbsCounts i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (0 : Fin 7)))

theorem seven_weight_eval (t : ℝ) : natEval countA7 t = ∑ i : Fin 7, t^(sevenWeight i) := by
  rw [← alphabet_seven_count]
  simp [natEval, weightPolynomial, Polynomial.eval₂_finset_sum, sevenWeight]

theorem real_subsequence_arithmetic :
    ((329:ℝ)/250)*natEval countE7 (((131:ℝ)/200)^2) < natEval countA7 ((131:ℝ)/200) := by
  norm_num [natEval, countA7, countA6, countE7, countE6]

theorem gibbsCounts_positive_margin :
    0 < typeEntropy gibbsCounts + (typeEnergy gibbsCounts:ℝ)*Real.log ((131:ℝ)/200) -
      (typeMass gibbsCounts:ℝ)*Real.log (((329:ℝ)/250)*natEval countE7 (((131:ℝ)/200)^2)) := by
  have ht : (0:ℝ) < 131/200 := by norm_num
  have hL : (0:ℝ) < (200:ℝ)^21 := by positivity
  have hent := gibbs_type_entropy sevenWeight gibbsCounts (131/200) ((200:ℝ)^21)
    ht hL gibbsCounts_scaled
  have hmass : (∑ i, (gibbsCounts i:ℝ)) = (typeMass gibbsCounts:ℝ) := by
    simp [typeMass]
  have henergy : (∑ i, (gibbsCounts i:ℝ)*(sevenWeight i:ℝ)) = (typeEnergy gibbsCounts:ℝ) := by
    unfold typeEnergy
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmass, henergy, ← seven_weight_eval] at hent
  have hE : 0 < natEval countE7 (((131:ℝ)/200)^2) := by
    norm_num [natEval, countE7, countE6]
  have hc : (0:ℝ) < 329/250 := by norm_num
  have hlog := Real.log_lt_log (mul_pos hc hE) real_subsequence_arithmetic
  have hM : (0:ℝ) < typeMass gibbsCounts := by exact_mod_cast gibbsCounts_mass_pos
  have hp := mul_pos hM (sub_pos.mpr hlog)
  rw [hent]
  nlinarith only [hp]

/-- The full `1.316^d` statement, not a conditional reduction or an arithmetic proxy. -/
theorem subsequence_chromatic : SubsequenceTarget := by
  apply fixed_type_subsequence gibbsCounts ((131:ℝ)/200) ((329:ℝ)/250)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [natEval, countE7, countE6]) gibbsCounts_mass_pos gibbsCounts_energy_pos
  exact gibbsCounts_positive_margin

end HoffmanChromatic
