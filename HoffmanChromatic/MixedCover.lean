import HoffmanChromatic.HandTypes

/-! Exact interpolation: all covered layer levels, with fewer than 100 extra coordinates. -/
namespace HoffmanChromatic

open scoped BigOperators

theorem mixed_hand_score (u v : Fin 7 → ℕ) (s T : ℝ)
    (hm : typeMass u=typeMass v) (hu : T ≤ typeScore u s) (hv : T ≤ typeScore v s)
    (q j : ℕ) (hj : j ≤ q) :
    (q:ℝ)*T ≤ typeScore (fun i => (q-j)*u i+j*v i) s := by
  have hh : ((q-j:ℕ):ℝ)+(j:ℝ)=(q:ℝ) := by exact_mod_cast Nat.sub_add_cancel hj
  calc
    _ = ((q-j:ℕ):ℝ)*T+(j:ℝ)*T := by rw [← hh]; ring
    _ ≤ ((q-j:ℕ):ℝ)*typeScore u s+(j:ℝ)*typeScore v s :=
      add_le_add (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _))
    _ ≤ _ := typeScore_mix u v hm (q-j) j s

theorem mixed_hand_cover (q S : ℕ) (hlo : 150*q ≤ S) (hhi : S ≤ 300*q+1) :
    ∃ (m : Fin 7 → ℕ) (r : ℕ) (s : ℝ),
      typeMass m=200*q ∧ typeEnergy m+r=S ∧ r<100 ∧
      (s=3/8 ∨ s=12/25) ∧
      (q:ℝ)*(200*Real.log (13/10:ℝ)+Real.log (5/4:ℝ)) ≤ typeScore m s := by
  by_cases hmid : S ≤ 200*q
  · let j := (S-150*q)/50
    let r := (S-150*q)%50
    have hj : j ≤ q := by dsimp [j]; omega
    have hr : r<100 := by dsimp [r]; omega
    refine ⟨(fun i => (q-j)*handType0 i+j*handType1 i), r, 3/8, ?_, ?_, hr, Or.inl rfl, ?_⟩
    · rw [typeMass_mix, hand_type_masses.1, hand_type_masses.2.1]
      omega
    · rw [typeEnergy_mix, hand_type_energies.1, hand_type_energies.2.1]
      dsimp [j, r]
      omega
    · exact mixed_hand_score handType0 handType1 (3/8) _
        (by rw [hand_type_masses.1, hand_type_masses.2.1]) hand_score_0.le hand_score_1a.le q j hj
  · let j := (S-200*q)/100
    let r := (S-200*q)%100
    have hj : j ≤ q := by dsimp [j]; omega
    have hr : r<100 := by dsimp [r]; omega
    refine ⟨(fun i => (q-j)*handType1 i+j*handType2 i), r, 12/25, ?_, ?_, hr, Or.inr rfl, ?_⟩
    · rw [typeMass_mix, hand_type_masses.2.1, hand_type_masses.2.2]
      omega
    · rw [typeEnergy_mix, hand_type_energies.2.1, hand_type_energies.2.2]
      dsimp [j, r]
      omega
    · exact mixed_hand_score handType1 handType2 (12/25) _
        (by rw [hand_type_masses.2.1, hand_type_masses.2.2]) hand_score_1b.le hand_score_2.le q j hj

end HoffmanChromatic
