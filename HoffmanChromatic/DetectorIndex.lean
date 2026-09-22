import HoffmanChromatic.Detector
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.CharP.Two

/-!
The least binomial index of the prescribed detector on the entire window.
All statements are uniform in P; no enumeration of periods is used.
-/
namespace HoffmanChromatic

open scoped BigOperators Classical
open Polynomial

def prescribedDetector (P h : ℕ) : ZMod 2 :=
  if h = 0 ∨ h = P then 1 else 0

def detectorCoefficient (P j : ℕ) : ZMod 2 := 1 + (j.choose P : ZMod 2)

def binomialExpansion (c : ℕ → ZMod 2) (h : ℕ) : ZMod 2 :=
  ∑ j ∈ Finset.range (h+1), (h.choose j : ZMod 2) * c j

theorem binary_pascal_product (h k : ℕ) :
    (∑ j ∈ Finset.range (h+1), (h.choose j : ZMod 2) * (j.choose k : ZMod 2)) =
      if h = k then 1 else 0 := by
  have hx : ((X : Polynomial (ZMod 2)) + 1) + 1 = X := by
    have htwo : (2 : Polynomial (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
    linear_combination htwo
  have hp := congrArg (fun f : Polynomial (ZMod 2) => f.coeff k)
    (add_pow ((X : Polynomial (ZMod 2))+1) 1 h)
  rw [hx] at hp
  simp only [coeff_X_pow, finset_sum_coeff, one_pow, mul_one,
    coeff_mul_natCast, coeff_X_add_one_pow] at hp
  simpa only [mul_comm, eq_comm] using hp.symm

theorem detector_coefficient_expansion (P : ℕ) (hP : 0<P) (h : ℕ) :
    binomialExpansion (detectorCoefficient P) h = prescribedDetector P h := by
  have hzero := binary_pascal_product h 0
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one] at hzero
  simp only [binomialExpansion, detectorCoefficient, mul_add, mul_one,
    Finset.sum_add_distrib, hzero, binary_pascal_product, prescribedDetector]
  by_cases h0 : h=0 <;> by_cases hp : h=P <;> simp_all

theorem binary_choose_lucas (n k : ℕ) :
    (n.choose k : ZMod 2) =
      ((n%2).choose (k%2) : ZMod 2) * ((n/2).choose (k/2) : ZMod 2) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := 2)
  simpa only [Nat.cast_mul] using (ZMod.natCast_eq_natCast_iff _ _ 2).2 h

theorem binary_top_choose (P : ℕ) (hP : 0<P) :
    ((2*P-1).choose P : ZMod 2) = if ∃ ell : ℕ, P=2^ell then 1 else 0 := by
  induction P using Nat.strong_induction_on with
  | h P ih =>
    by_cases hmod : P%2=0
    · let k := P/2
      have hk : 0<k := by dsimp [k]; omega
      have hPk : P=2*k := by dsimp [k]; omega
      have hkP : k<P := by omega
      have hpow : (∃ ell : ℕ, P=2^ell) ↔ ∃ ell : ℕ, k=2^ell := by
        constructor
        · rintro ⟨ell,hell⟩
          cases ell with
          | zero => simp at hell; omega
          | succ ell =>
            refine ⟨ell,?_⟩
            rw [pow_succ] at hell
            omega
        · rintro ⟨ell,hell⟩
          exact ⟨ell+1,by rw [pow_succ,← hell,hPk]; omega⟩
      rw [binary_choose_lucas]
      have h1 : (2*P-1)%2=1 := by omega
      have h2 : (2*P-1)/2=2*k-1 := by omega
      rw [h1,hmod,h2]
      change (1:ZMod 2)*((2*k-1).choose k : ZMod 2)=_
      rw [one_mul,ih k hkP hk,hpow]
    · let k := P/2
      have hmod1 : P%2=1 := by omega
      have hPk : P=2*k+1 := by dsimp [k]; omega
      by_cases hk : k=0
      · have hp1 : P=1 := by omega
        have hpw : ∃ ell : ℕ, P=2^ell := ⟨0,by simpa using hp1⟩
        rw [if_pos hpw,hp1]
        norm_num
      · have hkpos : 0<k := Nat.pos_of_ne_zero hk
        have hpow : ¬∃ ell : ℕ, P=2^ell := by
          rintro ⟨ell,hell⟩
          cases ell with
          | zero => simp at hell; omega
          | succ ell => rw [pow_succ] at hell; omega
        rw [if_neg hpow,binary_choose_lucas]
        have h1 : (2*P-1)%2=1 := by omega
        have h2 : (2*P-1)/2=2*k := by omega
        rw [h1,hmod1,h2]
        change (1:ZMod 2)*((2*k).choose k : ZMod 2)=0
        rw [one_mul]
        exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ 2).2 (Nat.two_dvd_centralBinom_of_one_le hkpos)

/-- The ordinary binomial basis, viewed as functions on the nonnegative integers. -/
def binomialBasis (j : ℕ) : ℕ → ZMod 2 := fun h => (h.choose j : ZMod 2)

/-- The shifted basis includes the generalized value `choose (-1) j = (-1)^j`. -/
def shiftedBinomialBasis (j : ℕ) : ℕ → ZMod 2 :=
  fun h => if h = 0 then 1 else ((h-1).choose j : ZMod 2)

def binomialSpan (D : ℕ) : Submodule (ZMod 2) (ℕ → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ j ≤ D, v = binomialBasis j}

def shiftedBinomialSpan (D : ℕ) : Submodule (ZMod 2) (ℕ → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ j ≤ D, v = shiftedBinomialBasis j}

theorem shifted_binomial_prefix (j : ℕ) :
    shiftedBinomialBasis j = ∑ i ∈ Finset.range (j+1), binomialBasis i := by
  funext h
  simp only [Finset.sum_apply, binomialBasis, shiftedBinomialBasis]
  cases h with
  | zero =>
    simp [Nat.choose_zero_succ, Finset.sum_range_succ']
  | succ h =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ, ← ih, Nat.choose_succ_succ, Nat.cast_add]
      have ht := CharTwo.add_self_eq_zero (h.choose j : ZMod 2)
      linear_combination -ht

theorem binomial_shifted_succ (j : ℕ) :
    binomialBasis (j+1) = shiftedBinomialBasis j + shiftedBinomialBasis (j+1) := by
  funext h
  cases h with
  | zero => simp [binomialBasis, shiftedBinomialBasis, CharTwo.add_self_eq_zero]
  | succ h => simp [binomialBasis, shiftedBinomialBasis, Nat.choose_succ_succ]

/-- Changing between the two binomial bases preserves every index bound. -/
theorem binomial_span_eq_shifted (D : ℕ) : binomialSpan D = shiftedBinomialSpan D := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨j, hj, rfl⟩
    cases j with
    | zero =>
      have he : binomialBasis 0 = shiftedBinomialBasis 0 := by
        funext h
        simp [binomialBasis, shiftedBinomialBasis]
      rw [he]
      exact Submodule.subset_span ⟨0, by omega, rfl⟩
    | succ j =>
      rw [binomial_shifted_succ]
      exact Submodule.add_mem _
        (Submodule.subset_span ⟨j, by omega, rfl⟩)
        (Submodule.subset_span ⟨j+1, hj, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro v ⟨j, hj, rfl⟩
    rw [shifted_binomial_prefix]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.subset_span ⟨i, by have := Finset.mem_range.mp hi; omega, rfl⟩

/-- A binomial expansion of index at most `D` on the whole distance window. -/
def HasBinomialDetector (P D : ℕ) : Prop :=
  ∃ f ∈ binomialSpan D, ∀ h < 2*P, f h = prescribedDetector P h

def HasShiftedBinomialDetector (P D : ℕ) : Prop :=
  ∃ f ∈ shiftedBinomialSpan D, ∀ h < 2*P, f h = prescribedDetector P h

theorem detector_basis_equivalence (P D : ℕ) :
    HasBinomialDetector P D ↔ HasShiftedBinomialDetector P D := by
  simp only [HasBinomialDetector, HasShiftedBinomialDetector, binomial_span_eq_shifted]

def binomialTransform (n : ℕ) : (ℕ → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun f := ∑ h ∈ Finset.range (n+1), (n.choose h : ZMod 2) * f h
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.mul_sum, mul_left_comm]

theorem binomial_transform_prescribed (P : ℕ) (hP : 0<P) (n : ℕ) :
    binomialTransform n (prescribedDetector P) = detectorCoefficient P n := by
  have he (h : ℕ) : prescribedDetector P h =
      (if h=0 then 1 else 0) + (if h=P then 1 else 0) := by
    by_cases h0 : h=0 <;> by_cases hp : h=P <;> simp_all [prescribedDetector]
  change (∑ h ∈ Finset.range (n+1), (n.choose h : ZMod 2) * prescribedDetector P h) = _
  simp only [he, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  by_cases hn : P ≤ n
  · simp [Finset.mem_range, show P < n+1 by omega, detectorCoefficient]
  · simp [Finset.mem_range, show ¬P < n+1 by omega,
      Nat.choose_eq_zero_of_lt (by omega : n<P), detectorCoefficient]

theorem binomial_transform_annihilates (D n : ℕ) (hDn : D<n)
    {f : ℕ → ZMod 2} (hf : f ∈ binomialSpan D) : binomialTransform n f = 0 := by
  have hs : binomialSpan D ≤ LinearMap.ker (binomialTransform n) := by
    apply Submodule.span_le.mpr
    rintro v ⟨j,hj,rfl⟩
    change (∑ h ∈ Finset.range (n+1), (n.choose h : ZMod 2) * (h.choose j : ZMod 2)) = 0
    rw [binary_pascal_product, if_neg (by omega)]
  exact hs hf

theorem detector_nonzero_coefficient_le (P D n : ℕ) (hP : 0<P)
    (hn : n<2*P) (hc : detectorCoefficient P n ≠ 0)
    (hd : HasBinomialDetector P D) : n ≤ D := by
  obtain ⟨f,hf,hs⟩ := hd
  by_contra hle
  apply hc
  rw [← binomial_transform_prescribed P hP]
  have he : binomialTransform n (prescribedDetector P) = binomialTransform n f := by
    change (∑ h ∈ Finset.range (n+1), (n.choose h : ZMod 2) * prescribedDetector P h) =
      ∑ h ∈ Finset.range (n+1), (n.choose h : ZMod 2) * f h
    apply Finset.sum_congr rfl
    intro h hh
    rw [hs h (by have := Finset.mem_range.mp hh; omega)]
  rw [he]
  exact binomial_transform_annihilates D n (by omega) hf

theorem full_window_detector_exists (P : ℕ) (hP : 0<P) :
    HasBinomialDetector P (2*P-1) := by
  let f : ℕ → ZMod 2 :=
    ∑ j ∈ Finset.range (2*P), detectorCoefficient P j • binomialBasis j
  refine ⟨f, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨j, by have := Finset.mem_range.mp hj; omega, rfl⟩
  · intro h hh
    have he : binomialExpansion (detectorCoefficient P) h = f h := by
      dsimp [binomialExpansion, f]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, binomialBasis]
      rw [Finset.sum_subset (Finset.range_mono (by omega : h+1 ≤ 2*P))]
      · apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _
      · intro j _ hj
        rw [Nat.choose_eq_zero_of_lt (by
          have : ¬j < h+1 := by simpa only [Finset.mem_range] using hj
          omega)]
        simp
    rw [← he, detector_coefficient_expansion P hP]

theorem power_two_detector_exists (ell : ℕ) :
    HasShiftedBinomialDetector (2^ell) (2^ell-1) := by
  refine ⟨shiftedBinomialBasis (2^ell-1), Submodule.subset_span ⟨_, le_rfl, rfl⟩, ?_⟩
  intro h hh
  exact binaryDetector_spec ell h hh

theorem binomial_detector_mono (P D E : ℕ) (hDE : D≤E)
    (h : HasBinomialDetector P D) : HasBinomialDetector P E := by
  obtain ⟨f,hf,hs⟩ := h
  refine ⟨f, ?_, hs⟩
  apply (Submodule.span_mono ?_) hf
  rintro v ⟨j,hj,rfl⟩
  exact ⟨j,hj.trans hDE,rfl⟩

/-- The least index is small exactly when the period is a power of two. -/
noncomputable def minimumDetectorIndex (P : ℕ) : ℕ :=
  if ∃ ell : ℕ, P=2^ell then P-1 else 2*P-1

theorem minimum_detector_coefficient (P : ℕ) (hP : 0<P) :
    detectorCoefficient P (minimumDetectorIndex P) = 1 := by
  by_cases hp : ∃ ell : ℕ, P=2^ell
  · simp [minimumDetectorIndex, hp, detectorCoefficient,
      Nat.choose_eq_zero_of_lt (by omega : P-1<P)]
  · simp [minimumDetectorIndex, hp, detectorCoefficient, binary_top_choose P hP]

theorem minimum_detector_index_iff (P D : ℕ) (hP : 0<P) :
    HasBinomialDetector P D ↔ minimumDetectorIndex P ≤ D := by
  constructor
  · intro hd
    apply detector_nonzero_coefficient_le P D (minimumDetectorIndex P) hP _ _ hd
    · unfold minimumDetectorIndex
      split_ifs <;> omega
    · rw [minimum_detector_coefficient P hP]
      exact one_ne_zero
  · intro hD
    apply binomial_detector_mono P (minimumDetectorIndex P) D hD
    by_cases hp : ∃ ell : ℕ, P=2^ell
    · obtain ⟨ell,hell⟩ := hp
      have he : minimumDetectorIndex P=P-1 := by
        simp [minimumDetectorIndex, show ∃ ell : ℕ, P=2^ell from ⟨ell,hell⟩]
      rw [he,hell]
      exact (detector_basis_equivalence _ _).mpr (power_two_detector_exists ell)
    · simpa [minimumDetectorIndex,hp] using full_window_detector_exists P hP

/-- The same exact minimum holds for the shifted basis used by the detector. -/
theorem minimum_shifted_detector_index_iff (P D : ℕ) (hP : 0<P) :
    HasShiftedBinomialDetector P D ↔ minimumDetectorIndex P ≤ D := by
  rw [← detector_basis_equivalence, minimum_detector_index_iff P D hP]

end HoffmanChromatic
