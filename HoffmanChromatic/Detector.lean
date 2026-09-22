import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-! The binary detector on the full distance window, for every power of two. -/

namespace HoffmanChromatic

theorem detector_choose_even (ell h : ℕ)
    (hlo : 2^ell < h) (hhi : h < 2 * 2^ell) :
    2 ∣ (h-1).choose (2^ell-1) := by
  have hp : 0 < 2^ell := pow_pos (by norm_num) _
  have hsum : h-1 = 2^ell + (h-1-2^ell) := by omega
  rw [hsum, Nat.add_choose_eq]
  apply Finset.dvd_sum
  intro ij hij
  have hs := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 = 0
  · have hr : h-1-2^ell < ij.2 := by omega
    rw [Nat.choose_eq_zero_of_lt hr, mul_zero]
    exact dvd_zero 2
  · apply dvd_mul_of_dvd_left
    exact Nat.prime_two.dvd_choose_pow hi (by omega)

/-- The value at zero is the generalized binomial coefficient with upper index -1. -/
def binaryDetector (ell h : ℕ) : ZMod 2 :=
  if h = 0 then 1 else ((h-1).choose (2^ell-1) : ZMod 2)

theorem binaryDetector_spec (ell h : ℕ) (hhi : h < 2 * 2^ell) :
    binaryDetector ell h = if h = 0 ∨ h = 2^ell then 1 else 0 := by
  have hp : 0 < 2^ell := pow_pos (by norm_num) _
  by_cases hz : h = 0
  · simp [binaryDetector, hz]
  by_cases he : h = 2^ell
  · simp [binaryDetector, hz, he]
  have hc : ((h-1).choose (2^ell-1) : ZMod 2) = 0 := by
    by_cases hlo : h < 2^ell
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ 2).2
        (detector_choose_even ell h (by omega) hhi)
  simp [binaryDetector, hz, he, hc]

end HoffmanChromatic
