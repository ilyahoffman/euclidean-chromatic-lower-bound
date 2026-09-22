import HoffmanChromatic.BinomialWindow
import Mathlib.Data.Finset.Max

/-! The unrestricted binomial upper bound, obtained from a mode in the central window. -/
namespace HoffmanChromatic

theorem binomialMass_recurrence (n k : ℕ) (hkn : k<n) (t : ℝ) :
    ((k:ℝ)+1)*(1-t)*binomialMass n (k+1) t = ((n-k:ℕ):ℝ)*t*binomialMass n k t := by
  have he : n-k=(n-(k+1))+1 := by omega
  have hc : (n.choose (k+1):ℝ)*((k:ℝ)+1)=(n.choose k:ℝ)*((n-k:ℕ):ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  have hh := congrArg (fun z : ℝ => z*(t^k*(1-t)^(n-(k+1))*t*(1-t))) hc
  dsimp only at hh
  unfold binomialMass
  rw [he, pow_succ, pow_succ]
  rw [he] at hh
  nlinarith only [hh]

theorem binomial_mode_central (n : ℕ) (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    ∃ j : ℕ, j≤n ∧ |(j:ℝ)-(n:ℝ)*t|≤1 ∧ ∀ k : ℕ, binomialMass n k t≤binomialMass n j t := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (n+1))
    (fun k => binomialMass n k t) (by exact ⟨0, by simp⟩)
  have hjn : j≤n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hjpos := binomialMass_pos hjn ht ht1
  have hjR : (0:ℝ)≤j := Nat.cast_nonneg _
  have hnR : (0:ℝ)≤n := Nat.cast_nonneg _
  have hleft : (n:ℝ)*t-(j:ℝ)≤1 := by
    by_cases hjn' : j<n
    · have hm := hmax (j+1) (by simp; omega)
      have hrec := binomialMass_recurrence n j hjn' t
      have hscale : 0 ≤ ((j:ℝ)+1)*(1-t) := mul_nonneg (by positivity) (by linarith)
      have hh := mul_le_mul_of_nonneg_left hm hscale
      rw [hrec] at hh
      rw [Nat.cast_sub hjn] at hh
      have hcoeff : ((n:ℝ)-(j:ℝ))*t ≤ ((j:ℝ)+1)*(1-t) := by
        exact (mul_le_mul_right hjpos).mp hh
      nlinarith only [hcoeff, ht.le]
    · have he : j=n := by omega
      rw [he]
      have hh := mul_le_mul_of_nonneg_left ht1.le hnR
      nlinarith only [hh]
  have hright : (j:ℝ)-(n:ℝ)*t≤1 := by
    by_cases hj0 : j=0
    · rw [hj0]
      have hh := mul_nonneg hnR ht.le
      norm_num only [Nat.cast_zero, zero_sub]
      linarith
    · have hjp : 0<j := Nat.pos_of_ne_zero hj0
      have hprev : j-1<n := by omega
      have hm := hmax (j-1) (by simp; omega)
      have hrec := binomialMass_recurrence n (j-1) hprev t
      have he : j-1+1=j := by omega
      rw [he] at hrec
      have hsubj : ((j-1:ℕ):ℝ)=(j:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
      have hsubn : ((n-(j-1):ℕ):ℝ)=(n:ℝ)-(j:ℝ)+1 := by
        rw [Nat.cast_sub (by omega), hsubj]
        ring
      rw [hsubj, hsubn] at hrec
      have hscale : 0≤((n:ℝ)-(j:ℝ)+1)*t := by
        have hnr : (j:ℝ)≤n := by exact_mod_cast hjn
        exact mul_nonneg (by linarith) ht.le
      have hh := mul_le_mul_of_nonneg_left hm hscale
      have hh' : (j:ℝ)*(1-t)*binomialMass n j t ≤
          ((n:ℝ)-(j:ℝ)+1)*t*binomialMass n j t := by
        nlinarith only [hh, hrec]
      have hcoeff := (mul_le_mul_right hjpos).mp hh'
      nlinarith only [hcoeff, ht1.le]
  refine ⟨j, hjn, abs_le.mpr ⟨by linarith, hright⟩, ?_⟩
  intro k
  by_cases hkn : k≤n
  · exact hmax k (by simp; omega)
  · have hz : n.choose k=0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [binomialMass, hz, Nat.cast_zero, zero_mul]
    exact hjpos.le

/-- Uniform upper bound at every index, not only in the central window. -/
theorem binomial_uniform_upper (a : ℝ) (ha : 0<a) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ k : ℕ, ∀ t : ℝ,
      a≤t → t≤1-a → binomialMass n k t*Real.sqrt (n:ℝ)≤C := by
  obtain ⟨c, C, hc, hC, N, hb⟩ := binomial_central_bounds a 1 ha (by norm_num)
  refine ⟨C, hC, max N 1, ?_⟩
  intro n hn k t hat hta
  have ht : 0<t := ha.trans_le hat
  have ht1 : t<1 := by linarith
  obtain ⟨j, hjn, hj, hmax⟩ := binomial_mode_central n t ht ht1
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hsqrt : (1:ℝ)≤Real.sqrt (n:ℝ) := by
    simpa using Real.sqrt_le_sqrt hn1
  have hwin : |(j:ℝ)-(n:ℝ)*t|≤(1:ℝ)*Real.sqrt (n:ℝ) := by simpa using hj.trans hsqrt
  have hu := (hb n (by omega) j t hat hta hwin).2
  exact (mul_le_mul_of_nonneg_right (hmax k) (Real.sqrt_nonneg _)).trans hu

end HoffmanChromatic
