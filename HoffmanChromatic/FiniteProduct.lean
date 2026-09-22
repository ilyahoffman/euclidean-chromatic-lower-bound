import HoffmanChromatic.FiniteLaw

/-! Product laws, first moments and variances as finite sums. -/
namespace HoffmanChromatic
open scoped BigOperators

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

noncomputable def iid (p : FiniteLaw Ω) (n : ℕ) : FiniteLaw (Fin n → Ω) where
  weight x := ∏ i, p.weight (x i)
  nonneg x := Finset.prod_nonneg fun i _ => p.nonneg (x i)
  total := by
    rw [← Fintype.prod_sum]
    simp only [p.total, Finset.prod_const_one]

def sumObs (f : Ω → ℝ) {n : ℕ} (x : Fin n → Ω) : ℝ := ∑ i, f (x i)

omit [Fintype Ω] in
theorem sumObs_cons (f : Ω → ℝ) {n : ℕ} (a : Ω) (x : Fin n → Ω) :
    sumObs f (Fin.cons a x)=f a+sumObs f x := by
  simp [sumObs, Fin.sum_univ_succ]

theorem sum_fun_succ {n : ℕ} (f : (Fin (n+1) → Ω) → ℝ) :
    (∑ x, f x) = ∑ a : Ω, ∑ x : Fin n → Ω, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Ω)).sum_comp f, Fintype.sum_prod_type]
  rfl

theorem iid_mean_succ (p : FiniteLaw Ω) (n : ℕ) (f : (Fin (n+1) → Ω) → ℝ) :
    (p.iid (n+1)).mean f=p.mean (fun a => (p.iid n).mean (fun x => f (Fin.cons a x))) := by
  unfold mean
  rw [sum_fun_succ]
  simp only [iid, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.mul_sum, mul_assoc]

theorem iid_mean_sum (p : FiniteLaw Ω) (f : Ω → ℝ) (n : ℕ) :
    (p.iid n).mean (sumObs f)=(n:ℝ)*p.mean f := by
  induction n with
  | zero => simp [mean, sumObs]
  | succ n ih =>
    rw [iid_mean_succ]
    simp_rw [sumObs_cons]
    simp only [mean_add, mean_const, ih]
    push_cast
    ring

theorem iid_second_moment_zero (p : FiniteLaw Ω) (g : Ω → ℝ) (hg : p.mean g=0) (n : ℕ) :
    (p.iid n).mean (fun x => (sumObs g x)^2)=(n:ℝ)*p.mean (fun a => (g a)^2) := by
  induction n with
  | zero => simp [mean, sumObs]
  | succ n ih =>
    have hzero : (p.iid n).mean (sumObs g)=0 := by rw [iid_mean_sum, hg, mul_zero]
    rw [iid_mean_succ]
    simp_rw [sumObs_cons, add_sq]
    simp only [mean_add, mean_const, mean_const_mul, hzero, mul_zero, add_zero, ih]
    push_cast
    ring

theorem sumObs_centered (p : FiniteLaw Ω) (f : Ω → ℝ) {n : ℕ} (x : Fin n → Ω) :
    sumObs (fun a => f a-p.mean f) x=sumObs f x-(n:ℝ)*p.mean f := by
  simp [sumObs, Finset.sum_sub_distrib]

theorem iid_variance (p : FiniteLaw Ω) (f : Ω → ℝ) (n : ℕ) :
    (p.iid n).mean (fun x => (sumObs f x-(n:ℝ)*p.mean f)^2)=
      (n:ℝ)*p.mean (fun a => (f a-p.mean f)^2) := by
  have h := iid_second_moment_zero p (fun a => f a-p.mean f) (mean_centered p f) n
  simpa only [sumObs_centered] using h

theorem variance_le_sq_of_bounds (p : FiniteLaw Ω) (f : Ω → ℝ) (B : ℝ)
    (hf : ∀ a, 0≤f a ∧ f a≤B) :
    p.mean (fun a => (f a-p.mean f)^2)≤B^2 := by
  have hm0 := p.mean_nonneg (fun a => (hf a).1)
  have hmB : p.mean f≤B := by
    rw [← p.mean_const B]
    exact p.mean_mono fun a => (hf a).2
  rw [← p.mean_const (B^2)]
  apply p.mean_mono
  intro a
  have habs : |f a-p.mean f|≤B := abs_le.mpr ⟨by linarith [(hf a).1], by linarith [(hf a).2]⟩
  have hh := mul_self_le_mul_self (abs_nonneg _) habs
  simpa only [← sq, sq_abs] using hh

end FiniteLaw
end HoffmanChromatic
