import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Explicit Newton witnesses for the two coordinate alphabets.

`newtonU z i j` is the quotient of the Newton evaluation
  product_{r < j} (z^i - z^r)
by `(z + 1)^e_j` in characteristic two. `newtonW` expresses the
monomials in the monic Newton basis. The small tables are witnesses;
the theorems below check every polynomial identity in Lean's kernel.
They hold for a formal indeterminate, not merely for numerical samples.
-/

namespace HoffmanChromatic

open scoped BigOperators
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

instance f2SeriesCharP : CharP (PowerSeries (ZMod 2)) 2 :=
  ⟨fun n => by
    rw [← map_natCast (PowerSeries.C (ZMod 2)) n, ← map_zero (PowerSeries.C (ZMod 2)),
      PowerSeries.C_injective.eq_iff]
    exact CharP.cast_eq_zero_iff (ZMod 2) 2 n⟩

theorem reduceSeriesNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : PowerSeries (ZMod 2)) = ((n % 2 : ℕ) : PowerSeries (ZMod 2)) :=
  CharP.cast_eq_mod _ 2 n

def newtonExponent : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 4
  | 4 => 8
  | 5 => 9
  | 6 => 11
  | _ => 0

noncomputable def newtonU (z : PowerSeries (ZMod 2)) : ℕ → ℕ → PowerSeries (ZMod 2)
  | 0, 0 => 1
  | 1, 0 => 1
  | 1, 1 => 1
  | 2, 0 => 1
  | 2, 1 => 1 + z
  | 2, 2 => z
  | 3, 0 => 1
  | 3, 1 => 1 + z + z^2
  | 3, 2 => z + z^2 + z^3
  | 3, 3 => z^3 + z^4 + z^5
  | 4, 0 => 1
  | 4, 1 => 1 + z + z^2 + z^3
  | 4, 2 => z + z^2 + z^4 + z^5
  | 4, 3 => z^3 + z^5 + z^6 + z^8
  | 4, 4 => z^6 + z^7 + z^8
  | 5, 0 => 1
  | 5, 1 => 1 + z + z^2 + z^3 + z^4
  | 5, 2 => z + z^2 + z^6 + z^7
  | 5, 3 => z^3 + z^6 + z^8 + z^11
  | 5, 4 => z^6 + z^8 + z^9 + z^10 + z^12
  | 5, 5 => z^10 + z^12 + z^13 + z^14 + z^16
  | 6, 0 => 1
  | 6, 1 => 1 + z + z^2 + z^3 + z^4 + z^5
  | 6, 2 => z + z^2 + z^5 + z^8 + z^9
  | 6, 3 => z^3 + z^8 + z^9 + z^14
  | 6, 4 => z^6 + z^9 + z^10 + z^11 + z^12 + z^13 + z^16
  | 6, 5 => z^10 + z^11 + z^13 + z^18 + z^20 + z^21
  | 6, 6 => z^15 + z^18 + z^19 + z^20 + z^21 + z^22 + z^25
  | _, _ => 0

noncomputable def newtonW (z : PowerSeries (ZMod 2)) : ℕ → ℕ → PowerSeries (ZMod 2)
  | 0, 0 => 1
  | 0, 1 => 1
  | 0, 2 => 1
  | 0, 3 => 1
  | 0, 4 => 1
  | 0, 5 => 1
  | 0, 6 => 1
  | 1, 1 => 1
  | 1, 2 => 1 + z
  | 1, 3 => 1 + z + z^2
  | 1, 4 => 1 + z + z^2 + z^3
  | 1, 5 => 1 + z + z^2 + z^3 + z^4
  | 1, 6 => 1 + z + z^2 + z^3 + z^4 + z^5
  | 2, 2 => 1
  | 2, 3 => 1 + z + z^2
  | 2, 4 => 1 + z + z^3 + z^4
  | 2, 5 => 1 + z + z^5 + z^6
  | 2, 6 => 1 + z + z^4 + z^7 + z^8
  | 3, 3 => 1
  | 3, 4 => 1 + z + z^2 + z^3
  | 3, 5 => 1 + z + z^5 + z^6
  | 3, 6 => 1 + z + z^3 + z^4 + z^5 + z^6 + z^8 + z^9
  | 4, 4 => 1
  | 4, 5 => 1 + z + z^2 + z^3 + z^4
  | 4, 6 => 1 + z + z^4 + z^7 + z^8
  | 5, 5 => 1
  | 5, 6 => 1 + z + z^2 + z^3 + z^4 + z^5
  | 6, 6 => 1
  | _, _ => 0

private theorem newton_entry_6_0_0 (z : PowerSeries (ZMod 2)) :
    z^(0 * 0) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (0)) + ((z+1)^3 * ((0) * (0)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf

private theorem newton_entry_6_0_1 (z : PowerSeries (ZMod 2)) :
    z^(0 * 1) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (1)) + ((z+1)^3 * ((0) * (0)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf

private theorem newton_entry_6_0_2 (z : PowerSeries (ZMod 2)) :
    z^(0 * 2) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (1 + z)) + ((z+1)^3 * ((0) * (1)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf

private theorem newton_entry_6_0_3 (z : PowerSeries (ZMod 2)) :
    z^(0 * 3) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (1 + z + z^2)) + ((z+1)^3 * ((0) * (1 + z + z^2)) + ((z+1)^4 * ((0) * (1)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf

private theorem newton_entry_6_0_4 (z : PowerSeries (ZMod 2)) :
    z^(0 * 4) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((0) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((0) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((0) * (1)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf

private theorem newton_entry_6_0_5 (z : PowerSeries (ZMod 2)) :
    z^(0 * 5) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((0) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((0) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((0) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((0) * (1)) + (0))))))
  ring_nf

private theorem newton_entry_6_1_0 (z : PowerSeries (ZMod 2)) :
    z^(1 * 0) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (0)) + ((z+1)^3 * ((0) * (0)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf

private theorem newton_entry_6_1_1 (z : PowerSeries (ZMod 2)) :
    z^(1 * 1) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^1 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (1)) + ((z+1)^3 * ((0) * (0)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_1_2 (z : PowerSeries (ZMod 2)) :
    z^(1 * 2) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^2 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (1 + z)) + ((z+1)^3 * ((0) * (1)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_1_3 (z : PowerSeries (ZMod 2)) :
    z^(1 * 3) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^3 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (1 + z + z^2)) + ((z+1)^3 * ((0) * (1 + z + z^2)) + ((z+1)^4 * ((0) * (1)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_1_4 (z : PowerSeries (ZMod 2)) :
    z^(1 * 4) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^4 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((0) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((0) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((0) * (1)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_1_5 (z : PowerSeries (ZMod 2)) :
    z^(1 * 5) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^5 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((0) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((0) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((0) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((0) * (1)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_2_0 (z : PowerSeries (ZMod 2)) :
    z^(2 * 0) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (0)) + ((z+1)^3 * ((z) * (0)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf

private theorem newton_entry_6_2_1 (z : PowerSeries (ZMod 2)) :
    z^(2 * 1) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^2 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (1)) + ((z+1)^3 * ((z) * (0)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_2_2 (z : PowerSeries (ZMod 2)) :
    z^(2 * 2) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^4 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (1 + z)) + ((z+1)^3 * ((z) * (1)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_2_3 (z : PowerSeries (ZMod 2)) :
    z^(2 * 3) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^6 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (1 + z + z^2)) + ((z+1)^3 * ((z) * (1 + z + z^2)) + ((z+1)^4 * ((0) * (1)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_2_4 (z : PowerSeries (ZMod 2)) :
    z^(2 * 4) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^8 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((z) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((0) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((0) * (1)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_2_5 (z : PowerSeries (ZMod 2)) :
    z^(2 * 5) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^10 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((z) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((0) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((0) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((0) * (1)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_3_0 (z : PowerSeries (ZMod 2)) :
    z^(3 * 0) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (0)) + ((z+1)^3 * ((z + z^2 + z^3) * (0)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf

private theorem newton_entry_6_3_1 (z : PowerSeries (ZMod 2)) :
    z^(3 * 1) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^3 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (1)) + ((z+1)^3 * ((z + z^2 + z^3) * (0)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_3_2 (z : PowerSeries (ZMod 2)) :
    z^(3 * 2) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^6 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (1 + z)) + ((z+1)^3 * ((z + z^2 + z^3) * (1)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_3_3 (z : PowerSeries (ZMod 2)) :
    z^(3 * 3) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^9 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (1 + z + z^2)) + ((z+1)^3 * ((z + z^2 + z^3) * (1 + z + z^2)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (1)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_3_4 (z : PowerSeries (ZMod 2)) :
    z^(3 * 4) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^12 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((z + z^2 + z^3) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((0) * (1)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_3_5 (z : PowerSeries (ZMod 2)) :
    z^(3 * 5) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^15 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((z + z^2 + z^3) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((0) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((0) * (1)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_4_0 (z : PowerSeries (ZMod 2)) :
    z^(4 * 0) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (0)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (0)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (0)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf

private theorem newton_entry_6_4_1 (z : PowerSeries (ZMod 2)) :
    z^(4 * 1) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^4 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (1)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (0)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (0)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_4_2 (z : PowerSeries (ZMod 2)) :
    z^(4 * 2) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^8 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (1 + z)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (1)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (0)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_4_3 (z : PowerSeries (ZMod 2)) :
    z^(4 * 3) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^12 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (1 + z + z^2)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (1 + z + z^2)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (1)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (0)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_4_4 (z : PowerSeries (ZMod 2)) :
    z^(4 * 4) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^16 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (1)) + ((z+1)^9 * ((0) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_4_5 (z : PowerSeries (ZMod 2)) :
    z^(4 * 5) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^20 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((0) * (1)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_5_0 (z : PowerSeries (ZMod 2)) :
    z^(5 * 0) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (0)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (0)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (0)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (0)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (0)) + (0))))))
  ring_nf

private theorem newton_entry_6_5_1 (z : PowerSeries (ZMod 2)) :
    z^(5 * 1) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^5 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (1)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (0)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (0)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (0)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_5_2 (z : PowerSeries (ZMod 2)) :
    z^(5 * 2) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^10 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (1 + z)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (1)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (0)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (0)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_5_3 (z : PowerSeries (ZMod 2)) :
    z^(5 * 3) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^15 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (1 + z + z^2)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (1 + z + z^2)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (1)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (0)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_5_4 (z : PowerSeries (ZMod 2)) :
    z^(5 * 4) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^20 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (1)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (0)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_6_5_5 (z : PowerSeries (ZMod 2)) :
    z^(5 * 5) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^25 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (1)) + (0))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

set_option maxHeartbeats 4000000 in
theorem newton_factor_6 (z : PowerSeries (ZMod 2)) (i b : Fin 6) :
    z^(i.val * b.val) = ∑ j : Fin 6,
      (z + 1)^newtonExponent j.val * (newtonU z i.val j.val * newtonW z j.val b.val) := by
  fin_cases i <;> fin_cases b
  · exact newton_entry_6_0_0 z
  · exact newton_entry_6_0_1 z
  · exact newton_entry_6_0_2 z
  · exact newton_entry_6_0_3 z
  · exact newton_entry_6_0_4 z
  · exact newton_entry_6_0_5 z
  · exact newton_entry_6_1_0 z
  · exact newton_entry_6_1_1 z
  · exact newton_entry_6_1_2 z
  · exact newton_entry_6_1_3 z
  · exact newton_entry_6_1_4 z
  · exact newton_entry_6_1_5 z
  · exact newton_entry_6_2_0 z
  · exact newton_entry_6_2_1 z
  · exact newton_entry_6_2_2 z
  · exact newton_entry_6_2_3 z
  · exact newton_entry_6_2_4 z
  · exact newton_entry_6_2_5 z
  · exact newton_entry_6_3_0 z
  · exact newton_entry_6_3_1 z
  · exact newton_entry_6_3_2 z
  · exact newton_entry_6_3_3 z
  · exact newton_entry_6_3_4 z
  · exact newton_entry_6_3_5 z
  · exact newton_entry_6_4_0 z
  · exact newton_entry_6_4_1 z
  · exact newton_entry_6_4_2 z
  · exact newton_entry_6_4_3 z
  · exact newton_entry_6_4_4 z
  · exact newton_entry_6_4_5 z
  · exact newton_entry_6_5_0 z
  · exact newton_entry_6_5_1 z
  · exact newton_entry_6_5_2 z
  · exact newton_entry_6_5_3 z
  · exact newton_entry_6_5_4 z
  · exact newton_entry_6_5_5 z

private theorem newton_entry_7_0_0 (z : PowerSeries (ZMod 2)) :
    z^(0 * 0) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (0)) + ((z+1)^3 * ((0) * (0)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf

private theorem newton_entry_7_0_1 (z : PowerSeries (ZMod 2)) :
    z^(0 * 1) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (1)) + ((z+1)^3 * ((0) * (0)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf

private theorem newton_entry_7_0_2 (z : PowerSeries (ZMod 2)) :
    z^(0 * 2) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (1 + z)) + ((z+1)^3 * ((0) * (1)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf

private theorem newton_entry_7_0_3 (z : PowerSeries (ZMod 2)) :
    z^(0 * 3) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (1 + z + z^2)) + ((z+1)^3 * ((0) * (1 + z + z^2)) + ((z+1)^4 * ((0) * (1)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf

private theorem newton_entry_7_0_4 (z : PowerSeries (ZMod 2)) :
    z^(0 * 4) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((0) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((0) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((0) * (1)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf

private theorem newton_entry_7_0_5 (z : PowerSeries (ZMod 2)) :
    z^(0 * 5) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((0) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((0) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((0) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((0) * (1)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf

private theorem newton_entry_7_0_6 (z : PowerSeries (ZMod 2)) :
    z^(0 * 6) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 0 j.val * newtonW z j.val 6) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((0) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^3 * ((0) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^4 * ((0) * (1 + z + z^3 + z^4 + z^5 + z^6 + z^8 + z^9)) + ((z+1)^8 * ((0) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^9 * ((0) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^11 * ((0) * (1)) + (0)))))))
  ring_nf

private theorem newton_entry_7_1_0 (z : PowerSeries (ZMod 2)) :
    z^(1 * 0) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (0)) + ((z+1)^3 * ((0) * (0)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf

private theorem newton_entry_7_1_1 (z : PowerSeries (ZMod 2)) :
    z^(1 * 1) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^1 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (1)) + ((z+1)^3 * ((0) * (0)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_1_2 (z : PowerSeries (ZMod 2)) :
    z^(1 * 2) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^2 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (1 + z)) + ((z+1)^3 * ((0) * (1)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_1_3 (z : PowerSeries (ZMod 2)) :
    z^(1 * 3) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^3 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (1 + z + z^2)) + ((z+1)^3 * ((0) * (1 + z + z^2)) + ((z+1)^4 * ((0) * (1)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_1_4 (z : PowerSeries (ZMod 2)) :
    z^(1 * 4) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^4 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((0) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((0) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((0) * (1)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_1_5 (z : PowerSeries (ZMod 2)) :
    z^(1 * 5) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^5 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((0) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((0) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((0) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((0) * (1)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_1_6 (z : PowerSeries (ZMod 2)) :
    z^(1 * 6) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 1 j.val * newtonW z j.val 6) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^6 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^3 * ((0) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^4 * ((0) * (1 + z + z^3 + z^4 + z^5 + z^6 + z^8 + z^9)) + ((z+1)^8 * ((0) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^9 * ((0) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^11 * ((0) * (1)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_2_0 (z : PowerSeries (ZMod 2)) :
    z^(2 * 0) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (0)) + ((z+1)^3 * ((z) * (0)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf

private theorem newton_entry_7_2_1 (z : PowerSeries (ZMod 2)) :
    z^(2 * 1) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^2 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (1)) + ((z+1)^3 * ((z) * (0)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_2_2 (z : PowerSeries (ZMod 2)) :
    z^(2 * 2) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^4 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (1 + z)) + ((z+1)^3 * ((z) * (1)) + ((z+1)^4 * ((0) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_2_3 (z : PowerSeries (ZMod 2)) :
    z^(2 * 3) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^6 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (1 + z + z^2)) + ((z+1)^3 * ((z) * (1 + z + z^2)) + ((z+1)^4 * ((0) * (1)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_2_4 (z : PowerSeries (ZMod 2)) :
    z^(2 * 4) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^8 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((z) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((0) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((0) * (1)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_2_5 (z : PowerSeries (ZMod 2)) :
    z^(2 * 5) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^10 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((z) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((0) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((0) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((0) * (1)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_2_6 (z : PowerSeries (ZMod 2)) :
    z^(2 * 6) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 2 j.val * newtonW z j.val 6) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^12 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^3 * ((z) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^4 * ((0) * (1 + z + z^3 + z^4 + z^5 + z^6 + z^8 + z^9)) + ((z+1)^8 * ((0) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^9 * ((0) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^11 * ((0) * (1)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_3_0 (z : PowerSeries (ZMod 2)) :
    z^(3 * 0) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (0)) + ((z+1)^3 * ((z + z^2 + z^3) * (0)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf

private theorem newton_entry_7_3_1 (z : PowerSeries (ZMod 2)) :
    z^(3 * 1) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^3 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (1)) + ((z+1)^3 * ((z + z^2 + z^3) * (0)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_3_2 (z : PowerSeries (ZMod 2)) :
    z^(3 * 2) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^6 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (1 + z)) + ((z+1)^3 * ((z + z^2 + z^3) * (1)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (0)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_3_3 (z : PowerSeries (ZMod 2)) :
    z^(3 * 3) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^9 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (1 + z + z^2)) + ((z+1)^3 * ((z + z^2 + z^3) * (1 + z + z^2)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (1)) + ((z+1)^8 * ((0) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_3_4 (z : PowerSeries (ZMod 2)) :
    z^(3 * 4) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^12 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((z + z^2 + z^3) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((0) * (1)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_3_5 (z : PowerSeries (ZMod 2)) :
    z^(3 * 5) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^15 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((z + z^2 + z^3) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((0) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((0) * (1)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_3_6 (z : PowerSeries (ZMod 2)) :
    z^(3 * 6) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 3 j.val * newtonW z j.val 6) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^18 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^3 * ((z + z^2 + z^3) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^4 * ((z^3 + z^4 + z^5) * (1 + z + z^3 + z^4 + z^5 + z^6 + z^8 + z^9)) + ((z+1)^8 * ((0) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^9 * ((0) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^11 * ((0) * (1)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_4_0 (z : PowerSeries (ZMod 2)) :
    z^(4 * 0) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (0)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (0)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (0)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf

private theorem newton_entry_7_4_1 (z : PowerSeries (ZMod 2)) :
    z^(4 * 1) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^4 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (1)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (0)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (0)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_4_2 (z : PowerSeries (ZMod 2)) :
    z^(4 * 2) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^8 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (1 + z)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (1)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (0)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_4_3 (z : PowerSeries (ZMod 2)) :
    z^(4 * 3) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^12 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (1 + z + z^2)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (1 + z + z^2)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (1)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (0)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_4_4 (z : PowerSeries (ZMod 2)) :
    z^(4 * 4) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^16 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (1)) + ((z+1)^9 * ((0) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_4_5 (z : PowerSeries (ZMod 2)) :
    z^(4 * 5) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^20 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((0) * (1)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_4_6 (z : PowerSeries (ZMod 2)) :
    z^(4 * 6) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 4 j.val * newtonW z j.val 6) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^24 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^3 * ((z + z^2 + z^4 + z^5) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^4 * ((z^3 + z^5 + z^6 + z^8) * (1 + z + z^3 + z^4 + z^5 + z^6 + z^8 + z^9)) + ((z+1)^8 * ((z^6 + z^7 + z^8) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^9 * ((0) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^11 * ((0) * (1)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_5_0 (z : PowerSeries (ZMod 2)) :
    z^(5 * 0) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (0)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (0)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (0)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (0)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf

private theorem newton_entry_7_5_1 (z : PowerSeries (ZMod 2)) :
    z^(5 * 1) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^5 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (1)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (0)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (0)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (0)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_5_2 (z : PowerSeries (ZMod 2)) :
    z^(5 * 2) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^10 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (1 + z)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (1)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (0)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (0)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_5_3 (z : PowerSeries (ZMod 2)) :
    z^(5 * 3) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^15 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (1 + z + z^2)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (1 + z + z^2)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (1)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (0)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_5_4 (z : PowerSeries (ZMod 2)) :
    z^(5 * 4) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^20 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (1)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (0)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_5_5 (z : PowerSeries (ZMod 2)) :
    z^(5 * 5) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^25 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (1)) + ((z+1)^11 * ((0) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_5_6 (z : PowerSeries (ZMod 2)) :
    z^(5 * 6) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 5 j.val * newtonW z j.val 6) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^30 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^3 * ((z + z^2 + z^6 + z^7) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^4 * ((z^3 + z^6 + z^8 + z^11) * (1 + z + z^3 + z^4 + z^5 + z^6 + z^8 + z^9)) + ((z+1)^8 * ((z^6 + z^8 + z^9 + z^10 + z^12) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^9 * ((z^10 + z^12 + z^13 + z^14 + z^16) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^11 * ((0) * (1)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_6_0 (z : PowerSeries (ZMod 2)) :
    z^(6 * 0) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 6 j.val * newtonW z j.val 0) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^0 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4 + z^5) * (0)) + ((z+1)^3 * ((z + z^2 + z^5 + z^8 + z^9) * (0)) + ((z+1)^4 * ((z^3 + z^8 + z^9 + z^14) * (0)) + ((z+1)^8 * ((z^6 + z^9 + z^10 + z^11 + z^12 + z^13 + z^16) * (0)) + ((z+1)^9 * ((z^10 + z^11 + z^13 + z^18 + z^20 + z^21) * (0)) + ((z+1)^11 * ((z^15 + z^18 + z^19 + z^20 + z^21 + z^22 + z^25) * (0)) + (0)))))))
  ring_nf

private theorem newton_entry_7_6_1 (z : PowerSeries (ZMod 2)) :
    z^(6 * 1) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 6 j.val * newtonW z j.val 1) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^6 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4 + z^5) * (1)) + ((z+1)^3 * ((z + z^2 + z^5 + z^8 + z^9) * (0)) + ((z+1)^4 * ((z^3 + z^8 + z^9 + z^14) * (0)) + ((z+1)^8 * ((z^6 + z^9 + z^10 + z^11 + z^12 + z^13 + z^16) * (0)) + ((z+1)^9 * ((z^10 + z^11 + z^13 + z^18 + z^20 + z^21) * (0)) + ((z+1)^11 * ((z^15 + z^18 + z^19 + z^20 + z^21 + z^22 + z^25) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_6_2 (z : PowerSeries (ZMod 2)) :
    z^(6 * 2) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 6 j.val * newtonW z j.val 2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^12 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4 + z^5) * (1 + z)) + ((z+1)^3 * ((z + z^2 + z^5 + z^8 + z^9) * (1)) + ((z+1)^4 * ((z^3 + z^8 + z^9 + z^14) * (0)) + ((z+1)^8 * ((z^6 + z^9 + z^10 + z^11 + z^12 + z^13 + z^16) * (0)) + ((z+1)^9 * ((z^10 + z^11 + z^13 + z^18 + z^20 + z^21) * (0)) + ((z+1)^11 * ((z^15 + z^18 + z^19 + z^20 + z^21 + z^22 + z^25) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_6_3 (z : PowerSeries (ZMod 2)) :
    z^(6 * 3) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 6 j.val * newtonW z j.val 3) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^18 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4 + z^5) * (1 + z + z^2)) + ((z+1)^3 * ((z + z^2 + z^5 + z^8 + z^9) * (1 + z + z^2)) + ((z+1)^4 * ((z^3 + z^8 + z^9 + z^14) * (1)) + ((z+1)^8 * ((z^6 + z^9 + z^10 + z^11 + z^12 + z^13 + z^16) * (0)) + ((z+1)^9 * ((z^10 + z^11 + z^13 + z^18 + z^20 + z^21) * (0)) + ((z+1)^11 * ((z^15 + z^18 + z^19 + z^20 + z^21 + z^22 + z^25) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_6_4 (z : PowerSeries (ZMod 2)) :
    z^(6 * 4) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 6 j.val * newtonW z j.val 4) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^24 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4 + z^5) * (1 + z + z^2 + z^3)) + ((z+1)^3 * ((z + z^2 + z^5 + z^8 + z^9) * (1 + z + z^3 + z^4)) + ((z+1)^4 * ((z^3 + z^8 + z^9 + z^14) * (1 + z + z^2 + z^3)) + ((z+1)^8 * ((z^6 + z^9 + z^10 + z^11 + z^12 + z^13 + z^16) * (1)) + ((z+1)^9 * ((z^10 + z^11 + z^13 + z^18 + z^20 + z^21) * (0)) + ((z+1)^11 * ((z^15 + z^18 + z^19 + z^20 + z^21 + z^22 + z^25) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_6_5 (z : PowerSeries (ZMod 2)) :
    z^(6 * 5) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 6 j.val * newtonW z j.val 5) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^30 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4 + z^5) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^3 * ((z + z^2 + z^5 + z^8 + z^9) * (1 + z + z^5 + z^6)) + ((z+1)^4 * ((z^3 + z^8 + z^9 + z^14) * (1 + z + z^5 + z^6)) + ((z+1)^8 * ((z^6 + z^9 + z^10 + z^11 + z^12 + z^13 + z^16) * (1 + z + z^2 + z^3 + z^4)) + ((z+1)^9 * ((z^10 + z^11 + z^13 + z^18 + z^20 + z^21) * (1)) + ((z+1)^11 * ((z^15 + z^18 + z^19 + z^20 + z^21 + z^22 + z^25) * (0)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

private theorem newton_entry_7_6_6 (z : PowerSeries (ZMod 2)) :
    z^(6 * 6) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z 6 j.val * newtonW z j.val 6) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^36 = (z+1)^0 * ((1) * (1)) + ((z+1)^1 * ((1 + z + z^2 + z^3 + z^4 + z^5) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^3 * ((z + z^2 + z^5 + z^8 + z^9) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^4 * ((z^3 + z^8 + z^9 + z^14) * (1 + z + z^3 + z^4 + z^5 + z^6 + z^8 + z^9)) + ((z+1)^8 * ((z^6 + z^9 + z^10 + z^11 + z^12 + z^13 + z^16) * (1 + z + z^4 + z^7 + z^8)) + ((z+1)^9 * ((z^10 + z^11 + z^13 + z^18 + z^20 + z^21) * (1 + z + z^2 + z^3 + z^4 + z^5)) + ((z+1)^11 * ((z^15 + z^18 + z^19 + z^20 + z^21 + z^22 + z^25) * (1)) + (0)))))))
  ring_nf
  simp only [reduceSeriesNat]
  norm_num

set_option maxHeartbeats 4000000 in
theorem newton_factor_7 (z : PowerSeries (ZMod 2)) (i b : Fin 7) :
    z^(i.val * b.val) = ∑ j : Fin 7,
      (z + 1)^newtonExponent j.val * (newtonU z i.val j.val * newtonW z j.val b.val) := by
  fin_cases i <;> fin_cases b
  · exact newton_entry_7_0_0 z
  · exact newton_entry_7_0_1 z
  · exact newton_entry_7_0_2 z
  · exact newton_entry_7_0_3 z
  · exact newton_entry_7_0_4 z
  · exact newton_entry_7_0_5 z
  · exact newton_entry_7_0_6 z
  · exact newton_entry_7_1_0 z
  · exact newton_entry_7_1_1 z
  · exact newton_entry_7_1_2 z
  · exact newton_entry_7_1_3 z
  · exact newton_entry_7_1_4 z
  · exact newton_entry_7_1_5 z
  · exact newton_entry_7_1_6 z
  · exact newton_entry_7_2_0 z
  · exact newton_entry_7_2_1 z
  · exact newton_entry_7_2_2 z
  · exact newton_entry_7_2_3 z
  · exact newton_entry_7_2_4 z
  · exact newton_entry_7_2_5 z
  · exact newton_entry_7_2_6 z
  · exact newton_entry_7_3_0 z
  · exact newton_entry_7_3_1 z
  · exact newton_entry_7_3_2 z
  · exact newton_entry_7_3_3 z
  · exact newton_entry_7_3_4 z
  · exact newton_entry_7_3_5 z
  · exact newton_entry_7_3_6 z
  · exact newton_entry_7_4_0 z
  · exact newton_entry_7_4_1 z
  · exact newton_entry_7_4_2 z
  · exact newton_entry_7_4_3 z
  · exact newton_entry_7_4_4 z
  · exact newton_entry_7_4_5 z
  · exact newton_entry_7_4_6 z
  · exact newton_entry_7_5_0 z
  · exact newton_entry_7_5_1 z
  · exact newton_entry_7_5_2 z
  · exact newton_entry_7_5_3 z
  · exact newton_entry_7_5_4 z
  · exact newton_entry_7_5_5 z
  · exact newton_entry_7_5_6 z
  · exact newton_entry_7_6_0 z
  · exact newton_entry_7_6_1 z
  · exact newton_entry_7_6_2 z
  · exact newton_entry_7_6_3 z
  · exact newton_entry_7_6_4 z
  · exact newton_entry_7_6_5 z
  · exact newton_entry_7_6_6 z

end HoffmanChromatic
