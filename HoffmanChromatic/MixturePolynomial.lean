import HoffmanChromatic.FiniteProduct
import HoffmanChromatic.BinomialPolynomial

/-! Conditioning on all coordinate values outside the pair {0,1}. -/
namespace HoffmanChromatic
open scoped BigOperators
open Polynomial

variable {A : Type*} [Fintype A]

noncomputable def recordLetterPolynomial (b : A → ℕ) (t : ℝ) : Option A → Polynomial ℝ
  | none => bernoulliPolynomial t
  | some a => X^(b a)

def recordZero : Option A → ℕ
  | none => 1
  | some _ => 0

def recordValue (b : A → ℕ) : Option A → ℕ
  | none => 0
  | some a => b a

def recordN {n : ℕ} (x : Fin n → Option A) : ℕ := ∑ i, recordZero (x i)
def recordR (b : A → ℕ) {n : ℕ} (x : Fin n → Option A) : ℕ := ∑ i, recordValue b (x i)

noncomputable def mixturePolynomial (p : FiniteLaw (Option A)) (b : A → ℕ) (t : ℝ) : Polynomial ℝ :=
  ∑ a, C (p.weight a)*recordLetterPolynomial b t a

omit [Fintype A] in
theorem record_letter_product (b : A → ℕ) (t : ℝ) (n : ℕ) (x : Fin n → Option A) :
    (∏ i, recordLetterPolynomial b t (x i))=X^(recordR b x)*(bernoulliPolynomial t)^(recordN x) := by
  have h : ∀ a, recordLetterPolynomial b t a=X^(recordValue b a)*(bernoulliPolynomial t)^(recordZero a) := by
    intro a
    cases a <;> simp [recordLetterPolynomial, recordValue, recordZero]
  simp only [h, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, recordR, recordN]

theorem mixturePolynomial_expansion (p : FiniteLaw (Option A)) (b : A → ℕ) (t : ℝ) (n : ℕ) :
    (mixturePolynomial p b t)^n = ∑ x : Fin n → Option A,
      C ((p.iid n).weight x)*(X^(recordR b x)*(bernoulliPolynomial t)^(recordN x)) := by
  have hpow : (mixturePolynomial p b t)^n = ∏ _i : Fin n, mixturePolynomial p b t := by simp
  rw [hpow]
  simp only [mixturePolynomial]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib, ← map_prod, record_letter_product]
  rfl

theorem mixturePolynomial_coeff (p : FiniteLaw (Option A)) (b : A → ℕ) (t : ℝ) (n m : ℕ) :
    ((mixturePolynomial p b t)^n).coeff m =
      (p.iid n).mean (fun x => binomialMassZ (recordN x) ((m:ℤ)-recordR b x) t) := by
  rw [mixturePolynomial_expansion]
  simp only [finset_sum_coeff, coeff_C_mul, shifted_bernoulli_coeff, FiniteLaw.mean]

omit [Fintype A] in
theorem recordN_le (n : ℕ) (x : Fin n → Option A) : recordN x≤n := by
  have h : ∀ i, recordZero (x i)≤1 := by intro i; cases x i <;> simp [recordZero]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simpa [recordN] using hh

theorem recordN_mean (p : FiniteLaw (Option A)) (n : ℕ) :
    (p.iid n).mean (fun x => (recordN x:ℝ))=(n:ℝ)*p.weight none := by
  have he : (fun x : Fin n → Option A => (recordN x:ℝ))=FiniteLaw.sumObs (fun a => (recordZero a:ℝ)) := by
    funext x
    simp [recordN, FiniteLaw.sumObs]
  rw [he, FiniteLaw.iid_mean_sum]
  simp [FiniteLaw.mean, Fintype.sum_option, recordZero]

theorem recordN_variance (p : FiniteLaw (Option A)) (n : ℕ) :
    (p.iid n).mean (fun x => ((recordN x:ℝ)-(n:ℝ)*p.weight none)^2)≤(n:ℝ) := by
  let f : Option A → ℝ := fun a => recordZero a
  have hf : ∀ a, 0≤f a ∧ f a≤1 := by intro a; cases a <;> norm_num [f, recordZero]
  have hv := FiniteLaw.variance_le_sq_of_bounds p f 1 hf
  have hm : p.mean f=p.weight none := by simp [FiniteLaw.mean, Fintype.sum_option, f, recordZero]
  have hs : ∀ x : Fin n → Option A, FiniteLaw.sumObs f x=(recordN x:ℝ) := by
    intro x; simp [FiniteLaw.sumObs, recordN, f]
  have hh := FiniteLaw.iid_variance p f n
  simp only [hm, hs] at hh
  rw [hh]
  simpa only [hm, one_pow, mul_one] using mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg n)

noncomputable def recordW (b : A → ℕ) (t : ℝ) {n : ℕ} (x : Fin n → Option A) : ℝ :=
  (recordR b x:ℝ)+t*(recordN x:ℝ)

noncomputable def recordMean (p : FiniteLaw (Option A)) (b : A → ℕ) (t : ℝ) : ℝ :=
  p.mean (fun a => (recordValue b a:ℝ)+t*(recordZero a:ℝ))

omit [Fintype A] in
theorem recordW_sum (b : A → ℕ) (t : ℝ) (n : ℕ) (x : Fin n → Option A) :
    recordW b t x=FiniteLaw.sumObs (fun a => (recordValue b a:ℝ)+t*(recordZero a:ℝ)) x := by
  simp [recordW, recordR, recordN, FiniteLaw.sumObs, Finset.sum_add_distrib, Finset.mul_sum]

theorem recordW_mean (p : FiniteLaw (Option A)) (b : A → ℕ) (t : ℝ) (n : ℕ) :
    (p.iid n).mean (recordW b t)=(n:ℝ)*recordMean p b t := by
  have he : (recordW b t : (Fin n → Option A) → ℝ)=
      FiniteLaw.sumObs (fun a => (recordValue b a:ℝ)+t*(recordZero a:ℝ)) := by
    funext x
    exact recordW_sum b t n x
  rw [he]
  exact FiniteLaw.iid_mean_sum _ _ _

theorem recordW_variance (p : FiniteLaw (Option A)) (b : A → ℕ) (t B : ℝ)
    (ht : 0≤t) (ht1 : t≤1) (hB : 1≤B) (hb : ∀ a, (b a:ℝ)≤B) (n : ℕ) :
    (p.iid n).mean (fun x => (recordW b t x-(n:ℝ)*recordMean p b t)^2)≤(n:ℝ)*B^2 := by
  let f : Option A → ℝ := fun a => (recordValue b a:ℝ)+t*(recordZero a:ℝ)
  have hf : ∀ a, 0≤f a ∧ f a≤B := by
    intro a
    cases a with
    | none => simpa [f, recordValue, recordZero] using And.intro ht (ht1.trans hB)
    | some a => simpa [f, recordValue, recordZero] using And.intro (show (0:ℝ)≤(b a:ℝ) from Nat.cast_nonneg (b a)) (hb a)
  have hv := FiniteLaw.variance_le_sq_of_bounds p f B hf
  have hh := FiniteLaw.iid_variance p f n
  simp_rw [recordW_sum]
  change (p.iid n).mean (fun x => (FiniteLaw.sumObs f x-(n:ℝ)*p.mean f)^2)≤(n:ℝ)*B^2
  rw [hh]
  exact mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg n)

end HoffmanChromatic
