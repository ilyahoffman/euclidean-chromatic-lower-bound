import HoffmanChromatic.SharpCrossing
import HoffmanChromatic.InteriorCertificates

/-! The four concave functions cover the full dyadic interval. -/
namespace HoffmanChromatic

theorem sharp_rate_cover (a : ℝ) (ha : Crossing a) (hheight : delta6 a<27/100) :
    (∀ δ : ℝ, a≤δ → δ≤11/20 → delta6 a≤delta6 δ) ∧
    (∀ δ : ℝ, 11/20≤δ → δ≤2*a → delta6 a≤delta7 δ) := by
  have ha0 : 0<a := by have hh := ha.1; linarith
  have h6L : mean01 tailE6 (342209/1000000)<(371979:ℝ)/1000000 := by
    norm_num [mean01,partition01,tailE6,Fin.sum_univ_succ]
  have h6U : (371980:ℝ)/1000000<mean01 tailE6 (342211/1000000) := by
    norm_num [mean01,partition01,tailE6,Fin.sum_univ_succ]
  obtain ⟨s6,hs6L,hs6U,hm6,hu6⟩ := saddle_exists_unique tailE6
    (342209/1000000) (342211/1000000) a (by norm_num) (by norm_num)
    (by linarith [ha.1]) (by linarith [ha.2.1])
  have hs6 : 0<s6 := by linarith
  have hs61 : s6<1 := by linarith
  have h7L : mean01 tailE7 (517230/1000000)<2*((371979:ℝ)/1000000) := by
    norm_num [mean01,partition01,tailE7,Fin.sum_univ_succ]
  have h7U : 2*((371980:ℝ)/1000000)<mean01 tailE7 (517232/1000000) := by
    norm_num [mean01,partition01,tailE7,Fin.sum_univ_succ]
  obtain ⟨s7,hs7L,hs7U,hm7,hu7⟩ := saddle_exists_unique tailE7
    (517230/1000000) (517232/1000000) (2*a) (by norm_num) (by norm_num)
    (by linarith [ha.1]) (by linarith [ha.2.1])
  norm_num at hs7L hs7U
  have hs7 : 0<s7 := by linarith
  have hs71 : s7<1 := by linarith
  have hleft : rateMinorant tailA6 tailE6 s6 a=delta6 a := by
    rw [rateMinorant_eq tailA6 tailE6 s6 a hs6 hs61 hm6,rateDelta_six]
  have hright : rateMinorant tailA7 tailE7 s7 (2*a)=delta6 a := by
    rw [rateMinorant_eq tailA7 tailE7 s7 (2*a) hs7 hs71 hm7,rateDelta_seven,← ha.2.2]
  have h1 := interior_minorant_1 s6 hs6L.le hs6U.le
  have h2 := interior_minorant_2 (2/5) (by norm_num) (by norm_num)
  have h3 := interior_minorant_3 (2/5) (by norm_num) (by norm_num)
  have h4 := interior_minorant_4 (12/25) (by norm_num) (by norm_num)
  have h5 := interior_minorant_5 (12/25) (by norm_num) (by norm_num)
  have h6 := interior_minorant_6 s7 hs7L.le hs7U.le
  constructor
  · intro δ hδL hδU
    have hδ0 : 0≤δ := ha0.le.trans hδL
    by_cases hc : δ≤21/50
    · have hh := rateMinorant_chord tailA6 tailE6 s6 a (21/50) δ (delta6 a)
        ha0.le (by norm_num) hδL hc (by rw [hleft]) (by linarith only [h1,hheight])
      have hu := rateMinorant_le tailA6 tailE6 s6 δ hs6 hs61 hδ0
      rw [rateDelta_six] at hu
      exact hh.trans hu
    · have hh := rateMinorant_chord tailA6 tailE6 (2/5) (21/50) (11/20) δ (delta6 a)
        (by norm_num) (by norm_num) (le_of_not_ge hc) hδU
        (by linarith only [h2,hheight]) (by linarith only [h3,hheight])
      have hu := rateMinorant_le tailA6 tailE6 (2/5) δ (by norm_num) (by norm_num) hδ0
      rw [rateDelta_six] at hu
      exact hh.trans hu
  · intro δ hδL hδU
    have hδ0 : 0≤δ := by linarith
    by_cases hc : δ≤17/25
    · have hh := rateMinorant_chord tailA7 tailE7 (12/25) (11/20) (17/25) δ (delta6 a)
        (by norm_num) (by norm_num) hδL hc
        (by linarith only [h4,hheight]) (by linarith only [h5,hheight])
      have hu := rateMinorant_le tailA7 tailE7 (12/25) δ (by norm_num) (by norm_num) hδ0
      rw [rateDelta_seven] at hu
      exact hh.trans hu
    · have hh := rateMinorant_chord tailA7 tailE7 s7 (17/25) (2*a) δ (delta6 a)
        (by norm_num) (by positivity) (le_of_not_ge hc) hδU
        (by linarith only [h6,hheight]) (by rw [hright])
      have hu := rateMinorant_le tailA7 tailE7 s7 δ hs7 hs71 hδ0
      rw [rateDelta_seven] at hu
      exact hh.trans hu

end HoffmanChromatic
