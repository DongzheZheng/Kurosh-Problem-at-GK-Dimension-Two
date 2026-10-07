import CriticalGK2.StemCutSupport

/-!
# A computed complete-support budget for actual common stems

The budget is the maximum of the actual complete prefix/suffix contraction
dimensions at every inside-stem cut and the actual dimension at the final
cut. It is proved to equal twice the actual maximum coefficient cut rank.
The concrete waiting operation preserves this computed quantity exactly.
-/

namespace CriticalGK2.ContractionBudget

noncomputable section

open TensorProduct

variable {F X Y : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]

theorem leftFlattening_tmul_range (x : X) (y : Y) (hy : y ≠ 0) :
    LinearMap.range (leftFlattening (x ⊗ₜ[F] y)) = Submodule.span F {x} := by
  apply le_antisymm
  · rintro z ⟨eta, rfl⟩
    rw [leftFlattening_apply, contractRight_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro z hz
    have hz0 : z = x := Set.mem_singleton_iff.mp hz
    subst z
    obtain ⟨eta, heta⟩ := Module.Projective.exists_dual_eq_one F hy
    exact ⟨eta, by simp only [leftFlattening_apply, contractRight_tmul, heta, one_smul]⟩

theorem tensorCutRank_tmul (x : X) (hx : x ≠ 0) (y : Y) (hy : y ≠ 0) :
    tensorCutRank (x ⊗ₜ[F] y) = 1 := by
  unfold tensorCutRank
  rw [leftFlattening_tmul_range x y hy]
  exact finrank_span_singleton hx

end

end CriticalGK2.ContractionBudget

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct CriticalGK2.ContractionBudget

variable (F : Type*) [Field F]

/-- The actual maximum full support dimension: both sides of every cut
inside the stem, and the dimension of the entire actual stem space at the
last cut. Scalar endpoint supports contribute at most the latter dimension. -/
def actualStemCutBudget (q : ℕ) (P : WordAlgebra F) : ℕ :=
  max ((Finset.range (q + 1)).sup fun a =>
    max (Module.finrank F (tensorPrefixSupport (actualStemInsideCutSpace F a (q - a) P)))
      (Module.finrank F (tensorSuffixSupport (actualStemInsideCutSpace F a (q - a) P))))
    (Module.finrank F (actualStemDualSpace F q P))

theorem polynomialCutRank_zero (q : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F q) (hP0 : P ≠ 0) : polynomialCutRank F 0 q P = 1 := by
  have h1 : (1 : WordAlgebra F) ∈ homogeneous F 0 := by
    rw [homogeneous_zero_eq_span_one]
    exact Submodule.subset_span (by simp)
  have hprod := ambientToDual_mul F 0 q 1 P h1 hP
  simp only [zero_add, one_mul] at hprod
  unfold polynomialCutRank wordCutRank wordCutTensor
  rw [hprod, LinearEquiv.symm_apply_apply]
  exact tensorCutRank_tmul (ambientToDual F 0 (1 : WordAlgebra F))
    (ambientToDual_ne_zero F 0 1 h1 one_ne_zero) (ambientToDual F q P)
      (ambientToDual_ne_zero F q P hP hP0)

theorem polynomialCutBudget_pos (q : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F q) (hP0 : P ≠ 0) : 1 ≤ polynomialCutBudget F q P := by
  have h : polynomialCutRank F 0 (q - 0) P ≤ polynomialCutBudget F q P := by
    change polynomialCutRank F 0 (q - 0) P ≤
      (Finset.range (q + 1)).sup (fun a => polynomialCutRank F a (q - a) P)
    exact Finset.le_sup (s := Finset.range (q + 1))
      (f := fun a : ℕ => polynomialCutRank F a (q - a) P) (b := 0)
      (Finset.mem_range.mpr (Nat.succ_pos q))
  simpa only [Nat.sub_zero, polynomialCutRank_zero F q P hP hP0] using h

theorem actualStemInsideCut_max_finrank (a b : ℕ) (P : WordAlgebra F) :
    max (Module.finrank F (tensorPrefixSupport (actualStemInsideCutSpace F a b P)))
      (Module.finrank F (tensorSuffixSupport (actualStemInsideCutSpace F a b P))) =
        2 * polynomialCutRank F a b P := by
  rw [actualStemInsideCut_prefixSupport_finrank, actualStemInsideCut_suffixSupport_finrank]
  omega

theorem finset_sup_twice {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    s.sup (fun i => 2 * f i) = 2 * s.sup f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      simp only [Finset.sup_insert, ih]
      omega

/-- The full budget of the actual common-stem space is precisely twice
the computed coefficient cut budget. -/
theorem actualStemCutBudget_eq_twice (q : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F q) (hP0 : P ≠ 0) :
    actualStemCutBudget F q P = 2 * polynomialCutBudget F q P := by
  have hpos := polynomialCutBudget_pos F q P hP hP0
  unfold actualStemCutBudget
  simp only [actualStemInsideCut_max_finrank]
  rw [finset_sup_twice, actualStemDualSpace_finrank F q P hP hP0]
  change max (2 * polynomialCutBudget F q P) 2 = 2 * polynomialCutBudget F q P
  omega

/-- Waiting preserves this actual full contraction-support budget. -/
theorem actualStemCutBudget_waiting (q : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F q) (hP0 : P ≠ 0) :
    actualStemCutBudget F (2 * q + 1) ((P * binaryLetter F false) * P) =
      actualStemCutBudget F q P := by
  have hwait : (P * binaryLetter F false) * P ∈ homogeneous F (2 * q + 1) := by
    have h := homogeneous_mul F
      (homogeneous_mul F hP (binaryLetter_mem_homogeneous F false)) hP
    have hd : (q + 1) + q = 2 * q + 1 := by omega
    rw [hd] at h
    exact h
  have hwait0 : (P * binaryLetter F false) * P ≠ 0 :=
    mul_ne_zero (mul_ne_zero hP0 (binaryLetter_ne_zero F false)) hP0
  rw [actualStemCutBudget_eq_twice F _ _ hwait hwait0,
    polynomialCutBudget_waiting F q P hP hP0,
    actualStemCutBudget_eq_twice F q P hP hP0]

theorem waitingStem_actualStemCutBudget (n : ℕ) (t : StemWord n → F) (ht : t ≠ 0) :
    actualStemCutBudget F (2 * n + 1) (waitingStem F n t) =
      actualStemCutBudget F n (stemPolynomial F n t) := by
  exact actualStemCutBudget_waiting F n (stemPolynomial F n t)
    ((wordHomogeneous_iff_mem_homogeneous F n _).mp (stemPolynomial_homogeneous F n t))
    (stemPolynomial_ne_zero F n t ht)

#print axioms CriticalGK2.Actual.actualStemCutBudget_eq_twice
#print axioms CriticalGK2.Actual.actualStemCutBudget_waiting

end

end CriticalGK2.Actual
