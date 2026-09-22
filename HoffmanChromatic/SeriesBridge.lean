import HoffmanChromatic.NewtonData
import HoffmanChromatic.Detector
import HoffmanChromatic.Geometry
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.CharP.Two

/-! Formal-series identities connecting Newton interpolation with the detector. -/

namespace HoffmanChromatic

open scoped BigOperators

abbrev F2Series := PowerSeries (ZMod 2)

/-- A genuine unit representing `1 + w`, so all integer powers are defined. -/
noncomputable def onePlusUnit : F2Seriesˣ :=
  (PowerSeries.invOneSubPow (ZMod 2) 1)⁻¹

theorem onePlusUnit_val : (onePlusUnit : F2Series) = 1 + PowerSeries.X := by
  change (PowerSeries.invOneSubPow (ZMod 2) 1).inv = _
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
  simp only [pow_one, CharTwo.sub_eq_add]

noncomputable def signedPower (h : ℤ) : F2Series := (onePlusUnit^h : F2Seriesˣ)

theorem signedPower_add (a b : ℤ) : signedPower (a+b) = signedPower a * signedPower b := by
  simp only [signedPower, zpow_add, Units.val_mul]

theorem signedPower_sum {I : Type*} (s : Finset I) (f : I → ℤ) :
    signedPower (∑ i ∈ s, f i) = ∏ i ∈ s, signedPower (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [signedPower]
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Finset.prod_insert ha,
      signedPower_add, ih]

theorem signedPower_nat (m : ℕ) : signedPower (m : ℤ) = (1 + PowerSeries.X)^m := by
  simp only [signedPower, zpow_natCast, Units.val_pow_eq_pow_val, onePlusUnit_val]

theorem signedPower_neg_one_coeff (D : ℕ) :
    PowerSeries.coeff (ZMod 2) D (signedPower (-1)) = 1 := by
  simp only [signedPower, zpow_neg_one, onePlusUnit, inv_inv]
  rw [PowerSeries.invOneSubPow_val_one_eq_invUnitSub_one, PowerSeries.coeff_invUnitsSub]
  simp

theorem coeff_onePlus_pow (m D : ℕ) :
    PowerSeries.coeff (ZMod 2) D ((1 + PowerSeries.X)^m) = (m.choose D : ZMod 2) := by
  have hc : (((Polynomial.X + Polynomial.C (1 : ZMod 2))^m : Polynomial (ZMod 2)) : F2Series) =
      (1 + PowerSeries.X)^m := by simp [add_comm]
  rw [← hc, Polynomial.coeff_coe, Polynomial.coeff_X_add_C_pow]
  simp

theorem signedPower_detector (ell h : ℕ) :
    PowerSeries.coeff (ZMod 2) (2^ell-1) (signedPower ((h : ℤ)-1)) =
      binaryDetector ell h := by
  by_cases hz : h = 0
  · subst h
    simp [signedPower_neg_one_coeff, binaryDetector]
  · have he : (h : ℤ) - 1 = ((h-1 : ℕ) : ℤ) := by omega
    rw [he, signedPower_nat, coeff_onePlus_pow]
    simp only [binaryDetector, if_neg hz]

noncomputable def inverseSeries : F2Series := signedPower (-1)

theorem inverseSeries_add_one : inverseSeries + 1 = PowerSeries.X * inverseSeries := by
  have hu : inverseSeries * (1 - PowerSeries.X) = 1 := by
    change ((onePlusUnit^(-1 : ℤ) : F2Seriesˣ) : F2Series) * _ = _
    simp only [zpow_neg_one, onePlusUnit, inv_inv,
      PowerSeries.invOneSubPow_val_one_eq_invUnitSub_one]
    simpa using PowerSeries.invUnitsSub_mul_sub (1 : (ZMod 2)ˣ)
  have htwo : (2 : F2Series) = 0 := CharP.cast_eq_zero _ 2
  rw [mul_sub, mul_one] at hu
  calc
    inverseSeries + 1 = (1 + inverseSeries * PowerSeries.X) + 1 := by
      exact congrArg (fun z : F2Series => z + 1) (eq_add_of_sub_eq hu)
    _ = PowerSeries.X * inverseSeries + 2 := by ring
    _ = PowerSeries.X * inverseSeries := by rw [htwo, add_zero]

theorem inverseSeries_pow (m : ℕ) : inverseSeries^m = signedPower (-(m:ℤ)) := by
  change ((onePlusUnit^(-1:ℤ) : F2Seriesˣ) : F2Series)^m = _
  rw [← Units.val_pow_eq_pow_val]
  unfold signedPower
  congr 1
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  ring

theorem row_series_identity {n : ℕ} (P : ℤ) (x y : Fin n → ℤ)
    (hx : layerLevel x = 2*P-1) (hy : layerLevel y = 2*P-1)
    (r s : ℕ) (hr : sqNorm x = 2*(r:ℤ)+1) (hs : sqNorm y = 2*(s:ℤ)+1) :
    signedPower (rho x y - 1) =
      signedPower (r:ℤ) * (∏ i, signedPower (-(x i * y i))) * signedPower (s:ℤ) := by
  rw [row_exponent_identity P x y hx hy r s hr hs]
  have he : (r:ℤ)+(s:ℤ)-(∑ i, x i*y i) =
      ((r:ℤ)+(∑ i, -(x i*y i)))+(s:ℤ) := by rw [Finset.sum_neg_distrib]; ring
  rw [he, signedPower_add, signedPower_add, signedPower_sum]

end HoffmanChromatic
