import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
Exact rational certificates printed in Appendix A.1 and the subsequence proof.
Terminating decimals below are written as fractions. `norm_num` produces
proof terms checked by Lean's kernel; no external verifier is assumed.
-/

namespace HoffmanChromatic

def A6 (t : ℚ) : ℚ := 1 + t + t^3 + t^6 + t^10 + t^15
def A7 (t : ℚ) : ℚ := A6 t + t^21
def E6 (s : ℚ) : ℚ := 1 + s + s^3 + s^4 + s^8 + s^9
def E7 (s : ℚ) : ℚ := E6 s + s^11

def mean7 (t : ℚ) : ℚ :=
  (t + 3*t^3 + 6*t^6 + 10*t^10 + 15*t^15 + 21*t^21) / A7 t

def rowRatio (E : ℚ → ℚ) (K u H : ℕ) : ℚ :=
  (200 : ℚ)^200 * ((u : ℚ)/200)^K /
    (((13 : ℚ)/10)^200 * E ((u : ℚ)/200)^200 * H)

def H1 : ℕ := 112^112 * 63^63 * 21^21 * 4^4
def H2 : ℕ := 100^100 * 64^64 * 28^28 * 7^7
def H3 : ℕ := 86^86 * 62^62 * 33^33 * 14^14 * 4^4

theorem row1_frequencies :
    112+63+21+4 = (200 : ℕ) ∧ 63+3*21+6*4 = 2*75 := by norm_num
theorem row2_frequencies :
    100+64+28+7+1 = (200 : ℕ) ∧ 64+3*28+6*7+10 = 2*100 := by norm_num
theorem row4_frequencies :
    86+62+33+14+4+1 = (200 : ℕ) ∧ 62+3*33+6*14+10*4+15 = 2*150 := by norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem integer_witness_1 : (5 : ℚ)/4 < rowRatio E6 75 75 H1 := by
  norm_num [rowRatio, E6, H1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem integer_witness_2 : (5 : ℚ)/4 < rowRatio E6 100 75 H2 := by
  norm_num [rowRatio, E6, H2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem integer_witness_3 : (5 : ℚ)/4 < rowRatio E7 100 96 H2 := by
  norm_num [rowRatio, E7, E6, H2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem integer_witness_4 : (5 : ℚ)/4 < rowRatio E7 150 96 H3 := by
  norm_num [rowRatio, E7, E6, H3]

theorem subsequence_A_lower : (203140 : ℚ)/100000 < A7 (131/200) := by
  norm_num [A7, A6]

theorem subsequence_E_upper : E7 (((131 : ℚ)/200)^2) < 154361/100000 := by
  norm_num [E7, E6]

theorem subsequence_margin :
    (1316 : ℚ)/1000 * (154361/100000) < 203140/100000 := by norm_num

theorem subsequence_mean_bounds :
    1 < mean7 (131/200) ∧ mean7 (131/200) < 11/10 := by
  norm_num [mean7, A7, A6]

theorem subsequence_ratio :
    (329 : ℚ)/250 < A7 (131/200) / E7 (((131 : ℚ)/200)^2) := by
  norm_num [A7, A6, E7, E6]

end HoffmanChromatic
