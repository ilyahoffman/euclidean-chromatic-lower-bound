import HoffmanChromatic.RateBracket

/-! Concave minorants and monotonicity tests for the crossing. -/
namespace HoffmanChromatic

variable {J K : Type*} [Fintype J] [Fintype K]

noncomputable def rateDelta (b : J → ℕ) (e : K → ℕ) (δ : ℝ) : ℝ :=
  logarithmicRate (partition01 b) (2*δ)-logarithmicRate (partition01 e) δ

noncomputable def rateMinorant (b : J → ℕ) (e : K → ℕ) (s δ : ℝ) : ℝ :=
  logarithmicRate (partition01 b) (2*δ)-Real.log (partition01 e s)+δ*Real.log s

theorem rateDelta_continuous (b : J → ℕ) (e : K → ℕ) :
    ContinuousOn (rateDelta b e) (Set.Ioi 0) := by
  have h2 : Continuous (fun x : ℝ => 2*x) := continuous_const.mul continuous_id
  have hA := (logarithmicRate01_continuous b).comp h2.continuousOn
    (fun x (hx : 0<x) => show 0<2*x by positivity)
  exact hA.sub (logarithmicRate01_continuous e)

theorem rateMinorant_concave (b : J → ℕ) (e : K → ℕ) (s : ℝ) :
    ConcaveOn ℝ (Set.Ici 0) (rateMinorant b e s) := by
  refine ⟨convex_Ici 0,?_⟩
  intro x hx y hy a d ha hd had
  have hh := (logarithmicRate01_concave b).2
    (show 0≤2*x from mul_nonneg (by norm_num) hx) (show 0≤2*y from mul_nonneg (by norm_num) hy) ha hd had
  change a*logarithmicRate (partition01 b) (2*x)+d*logarithmicRate (partition01 b) (2*y)≤
    logarithmicRate (partition01 b) (a*(2*x)+d*(2*y)) at hh
  have he : a*(2*x)+d*(2*y)=2*(a*x+d*y) := by ring
  rw [he] at hh
  change a*rateMinorant b e s x+d*rateMinorant b e s y≤rateMinorant b e s (a*x+d*y)
  calc
    _ = a*logarithmicRate (partition01 b) (2*x)+d*logarithmicRate (partition01 b) (2*y)-
        (a+d)*Real.log (partition01 e s)+(a*x+d*y)*Real.log s := by dsimp [rateMinorant]; ring
    _ = a*logarithmicRate (partition01 b) (2*x)+d*logarithmicRate (partition01 b) (2*y)-
        Real.log (partition01 e s)+(a*x+d*y)*Real.log s := by rw [had,one_mul]
    _ ≤ _ := add_le_add_right (sub_le_sub_right hh _) _

theorem rateMinorant_le (b : J → ℕ) (e : K → ℕ) (s δ : ℝ)
    (hs : 0<s) (hs1 : s<1) (hδ : 0≤δ) : rateMinorant b e s δ≤rateDelta b e δ := by
  have hh := logarithmicRate01_le e δ s hδ hs hs1
  dsimp [rateMinorant,rateDelta]
  linarith only [hh]

theorem rateMinorant_eq (b : J → ℕ) (e : K → ℕ) (s δ : ℝ)
    (hs : 0<s) (hs1 : s<1) (hmean : mean01 e s=δ) : rateMinorant b e s δ=rateDelta b e δ := by
  dsimp [rateMinorant,rateDelta]
  rw [logarithmicRate_at_saddle e s δ hs hs1 hmean]
  ring

theorem rateMinorant_chord (b : J → ℕ) (e : K → ℕ) (s l u v C : ℝ)
    (hl : 0≤l) (hu : 0≤u) (hvl : l≤v) (hvu : v≤u)
    (hL : C≤rateMinorant b e s l) (hU : C≤rateMinorant b e s u) :
    C≤rateMinorant b e s v := by
  exact (le_min hL hU).trans ((rateMinorant_concave b e s).ge_on_segment hl hu (Icc_subset_segment ⟨hvl,hvu⟩))

theorem partition01_mono (b : J → ℕ) (x y : ℝ) (hx : 0≤x) (hxy : x≤y) :
    partition01 b x≤partition01 b y := by
  have hs : (∑ j, x^(b j))≤∑ j, y^(b j) :=
    Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hx hxy _
  dsimp [partition01]
  linarith only [hs,hxy]

theorem rateMinorant_box_lower (b : J → ℕ) (e : K → ℕ) (δ s l u A₀ E₀ L₀ : ℝ)
    (hδ : 0≤δ) (hl : 0<l) (hls : l≤s) (hsu : s≤u)
    (hA : A₀≤logarithmicRate (partition01 b) (2*δ))
    (hE : Real.log (partition01 e u)≤E₀) (hL : L₀≤Real.log l) :
    A₀-E₀+δ*L₀≤rateMinorant b e s δ := by
  have hs : 0<s := hl.trans_le hls
  have hEp := Real.log_le_log (partition01_pos e s hs.le) (partition01_mono e s u hs.le hsu)
  have hLp := hL.trans (Real.log_le_log hl hls)
  have hp := mul_le_mul_of_nonneg_left hLp hδ
  dsimp [rateMinorant]
  linarith only [hA,hE,hEp,hp]

theorem rateDelta_strictMonoOn (b : J → ℕ) (e : K → ℕ) (D : Set ℝ) (tU sL : ℝ)
    (hD : ∀ δ∈D, 0≤δ) (hgap : tU^2<sL)
    (hb : ∀ δ∈D, ∃ t : ℝ, 0<t ∧ t<1 ∧ t≤tU ∧ mean01 b t=2*δ)
    (he : ∀ δ∈D, ∃ s : ℝ, 0<s ∧ s<1 ∧ sL≤s ∧ mean01 e s=δ) :
    StrictMonoOn (rateDelta b e) D := by
  intro x hx y hy hxy
  obtain ⟨tx,htx,htx1,htxU,hmtx⟩ := hb x hx
  obtain ⟨ty,hty,hty1,htyU,hmty⟩ := hb y hy
  obtain ⟨sx,hsx,hsx1,hsxL,hmsx⟩ := he x hx
  obtain ⟨sy,hsy,hsy1,hsyL,hmsy⟩ := he y hy
  have hA := (logarithmicRate_slope b (2*x) (2*y) tx ty
    (by have := hD x hx; positivity) (by have := hD y hy; positivity) htx htx1 hty hty1 hmtx hmty).1
  have hE := (logarithmicRate_slope e x y sx sy (hD x hx) (hD y hy) hsx hsx1 hsy hsy1 hmsx hmsy).2
  have hsq : ty^2≤tU^2 := by nlinarith only [mul_self_le_mul_self hty.le htyU]
  have hsqt : ty^2<sx := hsq.trans_lt (hgap.trans_le hsxL)
  have hlog := Real.log_lt_log (sq_pos_of_pos hty) hsqt
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hp := mul_pos (sub_pos.2 hxy) (sub_pos.2 hlog)
  dsimp [rateDelta]
  nlinarith only [hA,hE,hp]

theorem rateDelta_strictAntiOn (b : J → ℕ) (e : K → ℕ) (D : Set ℝ) (tL sU : ℝ)
    (hD : ∀ δ∈D, 0≤δ) (htL : 0<tL) (hgap : sU<tL^2)
    (hb : ∀ δ∈D, ∃ t : ℝ, 0<t ∧ t<1 ∧ tL≤t ∧ mean01 b t=2*δ)
    (he : ∀ δ∈D, ∃ s : ℝ, 0<s ∧ s<1 ∧ s≤sU ∧ mean01 e s=δ) :
    StrictAntiOn (rateDelta b e) D := by
  intro x hx y hy hxy
  obtain ⟨tx,htx,htx1,htxL,hmtx⟩ := hb x hx
  obtain ⟨ty,hty,hty1,htyL,hmty⟩ := hb y hy
  obtain ⟨sx,hsx,hsx1,hsxU,hmsx⟩ := he x hx
  obtain ⟨sy,hsy,hsy1,hsyU,hmsy⟩ := he y hy
  have hA := (logarithmicRate_slope b (2*x) (2*y) tx ty
    (by have := hD x hx; positivity) (by have := hD y hy; positivity) htx htx1 hty hty1 hmtx hmty).2
  have hE := (logarithmicRate_slope e x y sx sy (hD x hx) (hD y hy) hsx hsx1 hsy hsy1 hmsx hmsy).1
  have hsq : tL^2≤tx^2 := by nlinarith only [mul_self_le_mul_self htL.le htxL]
  have hgap' : sy<tx^2 := hsyU.trans_lt (hgap.trans_le hsq)
  have hlog := Real.log_lt_log hsy hgap'
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hp := mul_pos (sub_pos.2 hxy) (sub_pos.2 hlog)
  dsimp [rateDelta]
  nlinarith only [hA,hE,hp]

end HoffmanChromatic
