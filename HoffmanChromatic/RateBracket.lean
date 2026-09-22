import HoffmanChromatic.RateConcavity

/-! Finite bounds for a minimum and for changes in its mean parameter. -/
namespace HoffmanChromatic

variable {A : Type*} [Fintype A]

theorem logarithmicRate_bracket (b : A → ℕ) (l u m : ℝ)
    (hl : 0<l) (hlu : l<u) (hu1 : u<1) (hm : 0≤m)
    (hml : mean01 b l<m) (hmu : m<mean01 b u) :
    Real.log (partition01 b l)-m*Real.log l-
      (m-mean01 b l)*Real.log (u/l)≤logarithmicRate (partition01 b) m ∧
    logarithmicRate (partition01 b) m≤Real.log (partition01 b l)-m*Real.log l := by
  obtain ⟨x,hxl,hxu,hxm,huniq⟩ := saddle_exists_unique b l u m hl hlu hml hmu
  have hx : 0<x := hl.trans hxl
  have hu : 0<u := hl.trans hlu
  constructor
  · rw [logarithmicRate_at_saddle b x m hx (hxu.trans hu1) hxm,
      Real.log_div hu.ne' hl.ne']
    have ht := partition_log_tangent b l x hl hx
    have hlog := Real.log_le_log hx hxu.le
    have hshift : Real.log x-Real.log l≤Real.log u-Real.log l := by linarith only [hlog]
    have hmul := mul_le_mul_of_nonpos_left hshift (sub_nonpos.2 hml.le)
    nlinarith only [ht,hmul]
  · exact logarithmicRate01_le b m l hm hl (hlu.trans hu1)

/-- No derivative of the inverse mean is needed for these slope bounds. -/
theorem logarithmicRate_slope (b : A → ℕ) (m k x y : ℝ) (hm : 0≤m) (hk : 0≤k)
    (hx : 0<x) (hx1 : x<1) (hy : 0<y) (hy1 : y<1)
    (hmx : mean01 b x=m) (hky : mean01 b y=k) :
    -(k-m)*Real.log y≤logarithmicRate (partition01 b) k-logarithmicRate (partition01 b) m ∧
    logarithmicRate (partition01 b) k-logarithmicRate (partition01 b) m≤-(k-m)*Real.log x := by
  have h1 := logarithmicRate01_le b m y hm hy hy1
  have h2 := logarithmicRate01_le b k x hk hx hx1
  have hRm := logarithmicRate_at_saddle b x m hx hx1 hmx
  have hRk := logarithmicRate_at_saddle b y k hy hy1 hky
  constructor <;> nlinarith only [h1,h2,hRm,hRk]

theorem logarithmicRate_numeric_bound (b : A → ℕ) (l u m LZ UZ Ll Ul : ℝ)
    (hl : 0<l) (hlu : l<u) (hu1 : u<1) (hm : 0≤m)
    (hml : mean01 b l<m) (hmu : m<mean01 b u)
    (hZ : LZ≤Real.log (partition01 b l) ∧ Real.log (partition01 b l)≤UZ)
    (hx : Ll≤Real.log l ∧ Real.log l≤Ul) :
    LZ-m*Ul-(m-mean01 b l)*(u/l-1)≤logarithmicRate (partition01 b) m ∧
    logarithmicRate (partition01 b) m≤UZ-m*Ll := by
  have hb := logarithmicRate_bracket b l u m hl hlu hu1 hm hml hmu
  have hlog := Real.log_le_sub_one_of_pos (div_pos (hl.trans hlu) hl)
  have herr := mul_le_mul_of_nonneg_left hlog (sub_nonneg.2 hml.le)
  have hlower := mul_le_mul_of_nonneg_left hx.2 hm
  have hupper := mul_le_mul_of_nonneg_left hx.1 hm
  constructor <;> linarith only [hb.1,hb.2,hZ.1,hZ.2,hlower,hupper,herr]

end HoffmanChromatic
