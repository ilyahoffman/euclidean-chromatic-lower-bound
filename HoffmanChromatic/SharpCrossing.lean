import HoffmanChromatic.RateCover
import HoffmanChromatic.SharpCertificates

/-! Existence, bracketed uniqueness, and numerical enclosure of the sharp crossing. -/
namespace HoffmanChromatic

noncomputable def crossingLeft : ℝ := 371979/1000000
noncomputable def crossingRight : ℝ := 371980/1000000

theorem rateDelta_six (δ : ℝ) : rateDelta tailA6 tailE6 δ=delta6 δ := by
  have hA : partition01 tailA6=realA6 := funext partition01_A6
  have hE : partition01 tailE6=realE6 := funext partition01_E6
  simp only [rateDelta,delta6,hA,hE]

theorem rateDelta_seven (δ : ℝ) : rateDelta tailA7 tailE7 δ=delta7 δ := by
  have hA : partition01 tailA7=realA7 := funext partition01_A7
  have hE : partition01 tailE7=realE7 := funext partition01_E7
  simp only [rateDelta,delta7,hA,hE]

theorem crossing_six_increasing : StrictMonoOn delta6 (Set.Icc crossingLeft crossingRight) := by
  have hh := rateDelta_strictMonoOn tailA6 tailE6 (Set.Icc crossingLeft crossingRight)
    (563/1000) (342/1000)
    (by intro δ hδ; dsimp [crossingLeft] at hδ; linarith [hδ.1])
    (by norm_num)
    (by
      intro δ hδ
      have hL : mean01 tailA6 (562/1000)<2*crossingLeft := by
        norm_num [mean01,partition01,tailA6,Fin.sum_univ_succ,crossingLeft]
      have hU : 2*crossingRight<mean01 tailA6 (563/1000) := by
        norm_num [mean01,partition01,tailA6,Fin.sum_univ_succ,crossingRight]
      obtain ⟨t,htL,htU,hm,hu⟩ := saddle_exists_unique tailA6 (562/1000) (563/1000) (2*δ)
        (by norm_num) (by norm_num) (by linarith [hδ.1]) (by linarith [hδ.2])
      exact ⟨t,by linarith,by linarith,htU.le,hm⟩)
    (by
      intro δ hδ
      have hL : mean01 tailE6 (342/1000)<crossingLeft := by
        norm_num [mean01,partition01,tailE6,Fin.sum_univ_succ,crossingLeft]
      have hU : crossingRight<mean01 tailE6 (343/1000) := by
        norm_num [mean01,partition01,tailE6,Fin.sum_univ_succ,crossingRight]
      obtain ⟨s,hsL,hsU,hm,hu⟩ := saddle_exists_unique tailE6 (342/1000) (343/1000) δ
        (by norm_num) (by norm_num) (by linarith [hδ.1]) (by linarith [hδ.2])
      exact ⟨s,by linarith,by linarith,hsL.le,hm⟩)
  simpa only [show rateDelta tailA6 tailE6=delta6 from funext rateDelta_six] using hh

theorem crossing_seven_decreasing : StrictAntiOn delta7 (Set.Icc (2*crossingLeft) (2*crossingRight)) := by
  have hh := rateDelta_strictAntiOn tailA7 tailE7 (Set.Icc (2*crossingLeft) (2*crossingRight))
    (733/1000) (518/1000)
    (by intro δ hδ; dsimp [crossingLeft] at hδ; linarith [hδ.1])
    (by norm_num) (by norm_num)
    (by
      intro δ hδ
      have hL : mean01 tailA7 (733/1000)<2*(2*crossingLeft) := by
        norm_num [mean01,partition01,tailA7,Fin.sum_univ_succ,crossingLeft]
      have hU : 2*(2*crossingRight)<mean01 tailA7 (734/1000) := by
        norm_num [mean01,partition01,tailA7,Fin.sum_univ_succ,crossingRight]
      obtain ⟨t,htL,htU,hm,hu⟩ := saddle_exists_unique tailA7 (733/1000) (734/1000) (2*δ)
        (by norm_num) (by norm_num) (by linarith [hδ.1]) (by linarith [hδ.2])
      exact ⟨t,by linarith,by linarith,htL.le,hm⟩)
    (by
      intro δ hδ
      have hL : mean01 tailE7 (517/1000)<2*crossingLeft := by
        norm_num [mean01,partition01,tailE7,Fin.sum_univ_succ,crossingLeft]
      have hU : 2*crossingRight<mean01 tailE7 (518/1000) := by
        norm_num [mean01,partition01,tailE7,Fin.sum_univ_succ,crossingRight]
      obtain ⟨s,hsL,hsU,hm,hu⟩ := saddle_exists_unique tailE7 (517/1000) (518/1000) δ
        (by norm_num) (by norm_num) (by linarith [hδ.1]) (by linarith [hδ.2])
      exact ⟨s,by linarith,by linarith,hsU.le,hm⟩)
  simpa only [show rateDelta tailA7 tailE7=delta7 from funext rateDelta_seven] using hh

theorem sharp_crossing : ∃ a : ℝ, Crossing a ∧ (∀ b : ℝ, Crossing b → b=a) ∧
    (1309251:ℝ)/1000000<Real.exp (delta6 a) ∧ Real.exp (delta6 a)<(1309252:ℝ)/1000000 ∧
    delta6 a<27/100 := by
  let F : ℝ → ℝ := fun a => delta6 a-delta7 (2*a)
  have hL : F crossingLeft<0 := by
    have h6 := crossing_row_six_left.2
    have h7 := crossing_row_seven_left.1
    dsimp [F,crossingLeft]
    norm_num
    linarith only [h6,h7]
  have hU : 0<F crossingRight := by
    have h6 := crossing_row_six_right.1
    have h7 := crossing_row_seven_right.2
    dsimp [F,crossingRight]
    norm_num
    linarith only [h6,h7]
  have hC6 : ContinuousOn delta6 (Set.Ioi 0) := by
    simpa only [show rateDelta tailA6 tailE6=delta6 from funext rateDelta_six] using
      rateDelta_continuous tailA6 tailE6
  have hC7 : ContinuousOn delta7 (Set.Ioi 0) := by
    simpa only [show rateDelta tailA7 tailE7=delta7 from funext rateDelta_seven] using
      rateDelta_continuous tailA7 tailE7
  have hcont : ContinuousOn F (Set.Icc crossingLeft crossingRight) := by
    apply (hC6.mono ?_).sub
      (hC7.comp (continuous_const.mul continuous_id).continuousOn ?_)
    · intro a ha
      change 0<a
      have hh := ha.1
      dsimp [crossingLeft] at hh
      linarith
    · intro a ha
      change 0<2*a
      have hh := ha.1
      dsimp [crossingLeft] at hh
      linarith
  have hmono : StrictMonoOn F (Set.Icc crossingLeft crossingRight) := by
    intro x hx y hy hxy
    have h6 := crossing_six_increasing hx hy hxy
    have h7 := crossing_seven_decreasing
      (show 2*x∈Set.Icc (2*crossingLeft) (2*crossingRight) from ⟨by linarith [hx.1],by linarith [hx.2]⟩)
      (show 2*y∈Set.Icc (2*crossingLeft) (2*crossingRight) from ⟨by linarith [hy.1],by linarith [hy.2]⟩)
      (by linarith : 2*x<2*y)
    dsimp [F]
    linarith only [h6,h7]
  obtain ⟨a,ha,hFa⟩ := intermediate_value_Ioo
    (by norm_num [crossingLeft,crossingRight] : crossingLeft≤crossingRight) hcont
    (show (0:ℝ)∈Set.Ioo (F crossingLeft) (F crossingRight) from ⟨hL,hU⟩)
  have hca : Crossing a := ⟨ha.1,ha.2,sub_eq_zero.mp hFa⟩
  have haClosed : a∈Set.Icc crossingLeft crossingRight := ⟨ha.1.le,ha.2.le⟩
  have h6L := crossing_six_increasing (show crossingLeft∈Set.Icc crossingLeft crossingRight from
    ⟨le_rfl,by norm_num [crossingLeft,crossingRight]⟩) haClosed ha.1
  have h6U := crossing_six_increasing haClosed (show crossingRight∈Set.Icc crossingLeft crossingRight from
    ⟨by norm_num [crossingLeft,crossingRight],le_rfl⟩) ha.2
  have hlogL : Real.log ((1309251:ℝ)/1000000)<delta6 a := by
    have hr := crossing_row_six_left.1
    have hh := crossing_base_log_bounds.1
    dsimp [crossingLeft] at h6L
    linarith only [h6L,hr,hh]
  have hlogU : delta6 a<Real.log ((1309252:ℝ)/1000000) := by
    have hr := crossing_row_six_right.2
    have hh := crossing_base_log_bounds.2
    dsimp [crossingRight] at h6U
    linarith only [h6U,hr,hh]
  refine ⟨a,hca,?_,?_,?_,?_⟩
  · intro b hb
    apply hmono.injOn ⟨hb.1.le,hb.2.1.le⟩ haClosed
    dsimp [F]
    rw [hb.2.2,hca.2.2,sub_self,sub_self]
  · have hh := Real.exp_lt_exp.mpr hlogL
    rwa [Real.exp_log (by norm_num : (0:ℝ)<1309251/1000000)] at hh
  · have hh := Real.exp_lt_exp.mpr hlogU
    rwa [Real.exp_log (by norm_num : (0:ℝ)<1309252/1000000)] at hh
  · have hr := crossing_row_six_right.2
    dsimp [crossingRight] at h6U
    linarith only [h6U,hr]

end HoffmanChromatic
