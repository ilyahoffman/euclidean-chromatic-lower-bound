import HoffmanChromatic.TypeLogBound
import HoffmanChromatic.Subsequence

/-! The four short integer certificates, linked to entropy inequalities.
For the rounded bound all three types fit in the seven-letter alphabet.
-/
namespace HoffmanChromatic

open scoped BigOperators

def handType0 : Fin 7 → ℕ := ![0, 0, 21, 112, 63, 4, 0]
def handType1 : Fin 7 → ℕ := ![0, 1, 28, 100, 64, 7, 0]
def handType2 : Fin 7 → ℕ := ![0, 4, 33, 86, 62, 14, 1]

theorem hand_type_masses : typeMass handType0=200 ∧ typeMass handType1=200 ∧ typeMass handType2=200 := by
  norm_num [typeMass, handType0, handType1, handType2, Fin.sum_univ_succ]

theorem hand_type_energies : typeEnergy handType0=150 ∧ typeEnergy handType1=200 ∧ typeEnergy handType2=300 := by
  norm_num [typeEnergy, sevenWeight_values, handType0, handType1, handType2, Fin.sum_univ_succ]

def typeDenom (m : Fin 7 → ℕ) : ℕ := ∏ i, (m i)^(m i)

theorem typeDenom_pos (m : Fin 7 → ℕ) : 0 < typeDenom m := by
  apply Finset.prod_pos
  intro i _
  by_cases h : m i=0
  · simp [h]
  · exact pow_pos (Nat.pos_of_ne_zero h) _

theorem log_typeDenom (m : Fin 7 → ℕ) :
    Real.log (typeDenom m:ℝ) = ∑ i, (m i:ℝ)*Real.log (m i:ℝ) := by
  unfold typeDenom
  push_cast
  rw [Real.log_prod]
  · simp [Real.log_pow]
  · intro i _
    by_cases h : m i=0
    · simp [h]
    · exact pow_ne_zero _ (by exact_mod_cast h)

theorem typeEntropy_denom (m : Fin 7 → ℕ) :
    typeEntropy m = (typeMass m:ℝ)*Real.log (typeMass m:ℝ)-Real.log (typeDenom m:ℝ) := by
  simp only [typeEntropy, typeMass, Nat.cast_sum, log_typeDenom]

theorem score_of_integer_certificate (m : Fin 7 → ℕ) (K : ℕ) (s : ℝ)
    (hM : typeMass m=200) (hK : typeEnergy m=2*K) (hs : 0 < s)
    (hE : 0 < natEval countE7 s)
    (hcert : (5/4:ℝ)*((13/10:ℝ)^200)*(natEval countE7 s)^200*(typeDenom m:ℝ) <
      (200:ℝ)^200*s^K) :
    200*Real.log (13/10:ℝ)+Real.log (5/4:ℝ) < typeScore m s := by
  have hden : (0:ℝ) < typeDenom m := by exact_mod_cast typeDenom_pos m
  have hp : (0:ℝ) < (5/4:ℝ)*((13/10:ℝ)^200)*(natEval countE7 s)^200*(typeDenom m:ℝ) := by positivity
  have hh := Real.log_lt_log hp hcert
  simp only [Real.log_mul (by positivity : (5/4:ℝ)*((13/10:ℝ)^200)*(natEval countE7 s)^200 ≠ 0) hden.ne',
    Real.log_mul (by positivity : (5/4:ℝ)*((13/10:ℝ)^200) ≠ 0) (pow_ne_zero 200 hE.ne'),
    Real.log_mul (by norm_num : (5/4:ℝ) ≠ 0) (by norm_num : ((13/10:ℝ)^200) ≠ 0),
    Real.log_mul (by norm_num : ((200:ℝ)^200) ≠ 0) (pow_ne_zero K hs.ne'), Real.log_pow] at hh
  unfold typeScore
  rw [typeEntropy_denom, hM, hK]
  push_cast
  nlinarith only [hh]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem hand_score_0 : 200*Real.log (13/10:ℝ)+Real.log (5/4:ℝ) < typeScore handType0 (3/8) := by
  apply score_of_integer_certificate handType0 75 (3/8) hand_type_masses.1
    (by simpa using hand_type_energies.1) (by norm_num) (by norm_num [natEval, countE7, countE6])
  norm_num [natEval, countE7, countE6, typeDenom, handType0, Fin.prod_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem hand_score_1a : 200*Real.log (13/10:ℝ)+Real.log (5/4:ℝ) < typeScore handType1 (3/8) := by
  apply score_of_integer_certificate handType1 100 (3/8) hand_type_masses.2.1
    (by simpa using hand_type_energies.2.1) (by norm_num) (by norm_num [natEval, countE7, countE6])
  norm_num [natEval, countE7, countE6, typeDenom, handType1, Fin.prod_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem hand_score_1b : 200*Real.log (13/10:ℝ)+Real.log (5/4:ℝ) < typeScore handType1 (12/25) := by
  apply score_of_integer_certificate handType1 100 (12/25) hand_type_masses.2.1
    (by simpa using hand_type_energies.2.1) (by norm_num) (by norm_num [natEval, countE7, countE6])
  norm_num [natEval, countE7, countE6, typeDenom, handType1, Fin.prod_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem hand_score_2 : 200*Real.log (13/10:ℝ)+Real.log (5/4:ℝ) < typeScore handType2 (12/25) := by
  apply score_of_integer_certificate handType2 150 (12/25) hand_type_masses.2.2
    (by simpa using hand_type_energies.2.2) (by norm_num) (by norm_num [natEval, countE7, countE6])
  norm_num [natEval, countE7, countE6, typeDenom, handType2, Fin.prod_univ_succ]

end HoffmanChromatic
