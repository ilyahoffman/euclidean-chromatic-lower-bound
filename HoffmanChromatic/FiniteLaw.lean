import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite probability identities used in the coefficient conditioning argument. -/
namespace HoffmanChromatic

open scoped BigOperators

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ x, 0≤weight x
  total : ∑ x, weight x=1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

noncomputable def mean (p : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ x, p.weight x*f x
noncomputable def mass (p : FiniteLaw Ω) (S : Ω → Prop) : ℝ := by
  classical
  exact p.mean (fun x => if S x then 1 else 0)

theorem mean_const (p : FiniteLaw Ω) (c : ℝ) : p.mean (fun _ => c)=c := by
  simp only [mean, ← Finset.sum_mul, p.total, one_mul]

theorem mean_add (p : FiniteLaw Ω) (f g : Ω → ℝ) :
    p.mean (fun x => f x+g x)=p.mean f+p.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

theorem mean_sub (p : FiniteLaw Ω) (f g : Ω → ℝ) :
    p.mean (fun x => f x-g x)=p.mean f-p.mean g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mul_const (p : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    p.mean (fun x => f x*c)=p.mean f*c := by
  simp only [mean, ← mul_assoc, ← Finset.sum_mul]

theorem mean_const_mul (p : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    p.mean (fun x => c*f x)=c*p.mean f := by
  simp only [mean, mul_left_comm (p.weight _) c, Finset.mul_sum]

theorem mean_mono (p : FiniteLaw Ω) {f g : Ω → ℝ} (h : ∀ x, f x≤g x) :
    p.mean f≤p.mean g := by
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x)

theorem mean_nonneg (p : FiniteLaw Ω) {f : Ω → ℝ} (h : ∀ x, 0≤f x) : 0≤p.mean f := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (h x)

theorem mass_nonneg (p : FiniteLaw Ω) (S : Ω → Prop) : 0≤p.mass S := by
  classical
  exact p.mean_nonneg fun x => by split_ifs <;> norm_num

theorem mass_le_one (p : FiniteLaw Ω) (S : Ω → Prop) : p.mass S≤1 := by
  classical
  rw [← p.mean_const 1]
  apply p.mean_mono
  intro x
  split_ifs <;> norm_num

theorem mass_compl (p : FiniteLaw Ω) (S : Ω → Prop) :
    p.mass (fun x => ¬S x)=1-p.mass S := by
  classical
  unfold mass mean
  conv_rhs => rw [← p.total, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : S x <;> simp [hx, p.total]

theorem mass_union_le (p : FiniteLaw Ω) (S T : Ω → Prop) :
    p.mass (fun x => S x ∨ T x)≤p.mass S+p.mass T := by
  classical
  rw [mass, mass, mass, ← mean_add]
  apply p.mean_mono
  intro x
  split_ifs <;> simp_all

theorem mean_centered (p : FiniteLaw Ω) (f : Ω → ℝ) :
    p.mean (fun x => f x-p.mean f)=0 := by
  rw [mean_sub, mean_const, sub_self]

theorem shifted_second_moment (p : FiniteLaw Ω) (f : Ω → ℝ) (m : ℝ) :
    p.mean (fun x => (f x-m)^2)=p.mean (fun x => (f x-p.mean f)^2)+(p.mean f-m)^2 := by
  have h : (fun x => (f x-m)^2)=(fun x =>
      (f x-p.mean f)^2+(2*(p.mean f-m))*(f x-p.mean f)+(p.mean f-m)^2) := by
    funext x; ring
  rw [h, mean_add, mean_add, mean_const_mul, mean_centered, mul_zero, add_zero, mean_const]

/-- Chebyshev's inequality as an identity of finite weighted sums. -/
theorem chebyshev (p : FiniteLaw Ω) (f : Ω → ℝ) (m a : ℝ) (ha : 0≤a) :
    a^2*p.mass (fun x => a≤|f x-m|)≤p.mean (fun x => (f x-m)^2) := by
  classical
  rw [mass, ← mean_const_mul]
  apply p.mean_mono
  intro x
  dsimp only
  split_ifs with h
  · simp only [mul_one]
    have hh := mul_self_le_mul_self ha h
    simpa only [← sq, sq_abs] using hh
  · simp only [mul_zero]
    exact sq_nonneg _

theorem mass_mono (p : FiniteLaw Ω) {S T : Ω → Prop} (h : ∀ x, S x → T x) :
    p.mass S≤p.mass T := by
  classical
  unfold mass
  apply p.mean_mono
  intro x
  by_cases hS : S x
  · simp [hS, h x hS]
  · simp [hS]
    split_ifs <;> norm_num

theorem chebyshev_event (p : FiniteLaw Ω) (f : Ω → ℝ) (m a : ℝ) (ha : 0≤a)
    (S : Ω → Prop) (hS : ∀ x, S x → a≤|f x-m|) :
    a^2*p.mass S≤p.mean (fun x => (f x-m)^2) := by
  have hm := p.mass_mono hS
  exact (mul_le_mul_of_nonneg_left hm (sq_nonneg a)).trans (p.chebyshev f m a ha)

/-- Mean of an event-wise bounded function. -/
theorem mean_split_upper (p : FiniteLaw Ω) (S : Ω → Prop) (f : Ω → ℝ) (a b : ℝ)
    (hS : ∀ x, S x → f x≤a) (hT : ∀ x, ¬S x → f x≤b) :
    p.mean f≤a*p.mass S+b*(1-p.mass S) := by
  classical
  calc
    p.mean f ≤ a*p.mass S+b*p.mass (fun x => ¬S x) := by
      unfold mass
      rw [← mean_const_mul, ← mean_const_mul, ← mean_add]
      apply p.mean_mono
      intro x
      by_cases hx : S x
      · simpa [hx] using hS x hx
      · simpa [hx] using hT x hx
    _ = _ := by rw [mass_compl]

theorem mean_event_lower (p : FiniteLaw Ω) (S : Ω → Prop) (f : Ω → ℝ) (a : ℝ)
    (hf : ∀ x, 0≤f x) (hS : ∀ x, S x → a≤f x) :
    a*p.mass S≤p.mean f := by
  classical
  rw [mass, ← mean_const_mul]
  apply p.mean_mono
  intro x
  dsimp only
  split_ifs with h
  · simpa using hS x h
  · simpa using hf x

end FiniteLaw
end HoffmanChromatic
