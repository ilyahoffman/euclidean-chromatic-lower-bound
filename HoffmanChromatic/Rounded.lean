import HoffmanChromatic.MixedCover

/-! The complete uniform rounded endpoint, including all dimension choices. -/
namespace HoffmanChromatic

open scoped BigOperators Topology
open Filter

theorem rounded_error_absorption (B s : ℝ) : ∀ᶠ q : ℕ in atTop,
    B*(Real.log (200*(q:ℝ)+1)+1) + Real.log (150*(q:ℝ)+1) +
      300*Real.log (13/10:ℝ)-50*Real.log s+100*Real.log (natEval countE7 s) ≤
        (q:ℝ)*Real.log (5/4:ℝ) := by
  let C := B+300*Real.log (13/10:ℝ)-50*Real.log s+100*Real.log (natEval countE7 s)
  have h := (((log_affine_nat_div_zero 200 0).const_mul B).add (log_affine_nat_div_zero 150 0)).add
    (constant_div_nat_tendsto_zero C)
  simp only [mul_zero, zero_add, Nat.add_zero] at h
  have h' : Tendsto (fun q : ℕ => (B*Real.log (200*(q:ℝ)+1)+Real.log (150*(q:ℝ)+1)+C)/(q:ℝ))
      atTop (𝓝 0) := by
    apply h.congr'
    filter_upwards [] with q
    push_cast
    ring_nf
  have heps : (0:ℝ) < Real.log (5/4:ℝ) := Real.log_pos (by norm_num)
  have hh := h'.eventually (isOpen_Iio.mem_nhds heps)
  filter_upwards [hh, eventually_ge_atTop 1] with q hq hq1
  have hqR : (0:ℝ) < q := by exact_mod_cast (show 0<q by omega)
  have hm := (div_lt_iff₀ hqR).mp hq
  dsimp [C] at hm
  linarith

/-- Every sufficiently large dimension satisfies the stated base-1.30 bound. -/
theorem rounded_chromatic : RoundedTarget := by
  obtain ⟨B, _, hb⟩ := multinomial_entropy_lower (A := Fin 7)
  have hb' : ∀ m : Fin 7 → ℕ, typeEntropy m-B*(Real.log ((typeMass m:ℝ)+1)+1) ≤
      Real.log (Nat.multinomial Finset.univ m:ℝ) := by
    intro m
    simpa only [typeMass, Nat.cast_sum] using hb m
  have hevent := ((rounded_error_absorption B (3/8)).and (rounded_error_absorption B (12/25))).and
    (eventually_ge_atTop 1)
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨200*(q₀+1)+100, ?_⟩
  intro d hd
  let q := (d-100)/200
  have hd100 : 100 ≤ d := by omega
  have hq0 : q₀ ≤ q := by dsimp [q]; omega
  have hq1 : 0<q := by dsimp [q]; omega
  have hdim : 200*q+100 ≤ d ∧ d ≤ 200*q+300 := by dsimp [q]; omega
  obtain ⟨ell, hlo, hhi⟩ := dyadic_layer_cover q hq1
  obtain ⟨m, r, s, hm, he, hr, hs, hscore⟩ := mixed_hand_cover q (2*2^ell-1) hlo hhi
  have hs0 : 0<s := by rcases hs with rfl | rfl <;> norm_num
  have hs1 : s≤1 := by rcases hs with rfl | rfl <;> norm_num
  have hE : 1 ≤ natEval countE7 s := by
    rcases hs with rfl | rfl <;> norm_num [natEval, countE7, countE6]
  have herr := hq₀ q hq0
  have herrs : B*(Real.log (200*(q:ℝ)+1)+1) + Real.log (150*(q:ℝ)+1) +
      300*Real.log (13/10:ℝ)-50*Real.log s+100*Real.log (natEval countE7 s) ≤
        (q:ℝ)*Real.log (5/4:ℝ) := by
    rcases hs with rfl | rfl
    · exact herr.1.1
    · exact herr.1.2
  have hnd : typeMass m+r ≤ d := by omega
  intro k hc
  have hcol := colorable_of_dimension_le hnd hc
  have hlog := seven_type_log_bound B hb' m r ell k s hs0 hs1 hE hr he hcol
  have hp : 0 < (2:ℕ)^ell := pow_pos (by norm_num) _
  have hpR : (0:ℝ)<(2^ell:ℕ) := by exact_mod_cast hp
  have hple : (2:ℕ)^ell ≤ 150*q+1 := by omega
  have hpleR : ((2^ell:ℕ):ℝ) ≤ 150*(q:ℝ)+1 := by exact_mod_cast hple
  have hplog := Real.log_le_log hpR hpleR
  push_cast at hplog
  rw [hm] at hlog
  push_cast at hlog
  have hlC : 0 ≤ Real.log (13/10:ℝ) := Real.log_nonneg (by norm_num)
  have hdR : (d:ℝ) ≤ 200*(q:ℝ)+300 := by exact_mod_cast hdim.2
  have hdlog := mul_le_mul_of_nonneg_right hdR hlC
  have hfinal : (d:ℝ)*Real.log (13/10:ℝ) ≤ Real.log (k:ℝ) := by
    nlinarith only [hlog, hplog, hscore, herrs, hdlog]
  have hk : (0:ℝ)<k := by
    obtain ⟨c⟩ := hc
    have h := (c (0 : EuclideanSpace ℝ (Fin d))).isLt
    exact_mod_cast (show 0<k by omega)
  apply (Real.log_le_log_iff (pow_pos (by norm_num : (0:ℝ)<13/10) d) hk).mp
  rw [Real.log_pow]
  exact hfinal

end HoffmanChromatic
