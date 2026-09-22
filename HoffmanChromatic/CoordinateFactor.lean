import HoffmanChromatic.SeriesBridge

/-! The one-coordinate factorization on each consecutive integer alphabet. -/

namespace HoffmanChromatic

open scoped BigOperators

theorem newton_factor (Q : ℕ) (hQ : Q = 6 ∨ Q = 7) (z : F2Series) (i b : Fin Q) :
    z^(i.val*b.val) = ∑ j : Fin Q,
      (z+1)^newtonExponent j.val * (newtonU z i.val j.val * newtonW z j.val b.val) := by
  rcases hQ with rfl | rfl
  · exact newton_factor_6 z i b
  · exact newton_factor_7 z i b

def intervalLetter {Q : ℕ} (L : ℤ) (i : Fin Q) : ℤ := L + i.val

theorem intervalLetter_injective (Q : ℕ) (L : ℤ) :
    Function.Injective (@intervalLetter Q L) := by
  intro i j h
  apply Fin.ext
  unfold intervalLetter at h
  omega

theorem shifted_kernel (Q : ℕ) (L : ℤ) (i b : Fin Q) :
    signedPower (-(intervalLetter L i * intervalLetter L b)) =
      signedPower (-(L^2) - L*i.val) * inverseSeries^(i.val*b.val) *
        signedPower (-(L*b.val)) := by
  rw [inverseSeries_pow, ← signedPower_add, ← signedPower_add]
  apply congrArg signedPower
  unfold intervalLetter
  push_cast
  ring

noncomputable def coordinateU {Q : ℕ} (L : ℤ) (j i : Fin Q) : F2Series :=
  signedPower (-(L^2)-L*i.val) *
    (inverseSeries^newtonExponent j.val * newtonU inverseSeries i.val j.val)

noncomputable def coordinateW {Q : ℕ} (L : ℤ) (j b : Fin Q) : F2Series :=
  newtonW inverseSeries j.val b.val * signedPower (-(L*b.val))

theorem coordinate_factorization (Q : ℕ) (hQ : Q = 6 ∨ Q = 7) (L : ℤ) (i b : Fin Q) :
    signedPower (-(intervalLetter L i * intervalLetter L b)) =
      ∑ j : Fin Q, PowerSeries.X^newtonExponent j.val *
        (coordinateU L j i * coordinateW L j b) := by
  rw [shifted_kernel, newton_factor Q hQ, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [inverseSeries_add_one, mul_pow]
  unfold coordinateU coordinateW
  ac_rfl

end HoffmanChromatic
