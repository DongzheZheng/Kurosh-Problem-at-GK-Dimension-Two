import CriticalGK2.HomogeneousIdealQuotient
import CriticalGK2.GenericNormalLower
import Mathlib.Algebra.DirectSum.Module

/-!
# The actual grading of an actual homogeneous word-ideal quotient

The degree spaces are the literal images of H_n in H/I. Every quotient
element has a finite homogeneous decomposition, obtained from a free-word
representative. Relations between distinct degrees are isolated by the
actual coefficient projections and the actual homogeneity of I. Thus the
canonical direct-sum map is bijective. Multiplication respects the literal
degree spaces by the actual homogeneous free-word multiplication theorem.

Homogeneity of the ideal is the hypothesis for these grading results.
-/

namespace CriticalGK2.HomogeneousGrading

noncomputable section

open CriticalGK2.Actual
open scoped BigOperators DirectSum

variable (F : Type*) [Field F]

/-- The actual degree-n image in the literal quotient H/I. -/
def degreeSpace (I : TwoSidedIdeal (WordAlgebra F)) (n : ℕ) :
    Submodule F (WordIdealQuotient F I) :=
  CriticalGK2.GenericLower.degreeImage F (wordIdealQuotientMap F I) n

instance degreeSpace_finite (I : TwoSidedIdeal (WordAlgebra F)) (n : ℕ) :
    FiniteDimensional F (degreeSpace F I n) :=
  inferInstanceAs (FiniteDimensional F
    (CriticalGK2.GenericLower.degreeImage F (wordIdealQuotientMap F I) n))

/-- Outside the literal degree support, the actual projection is zero. -/
theorem homogeneousProjection_eq_zero_of_not_mem_degreeSupport
    (P : WordAlgebra F) (n : ℕ) (hn : n ∉ wordDegreeSupport F P) :
    (homogeneousProjection F n P).val = 0 := by
  classical
  apply Finsupp.ext
  intro w
  rw [homogeneousProjection_coeff]
  change (if w.length = n then P w else 0) = 0
  by_cases hw : w.length = n
  · rw [if_pos hw]
    apply Finsupp.notMem_support_iff.mp
    intro hws
    apply hn
    exact Finset.mem_image.mpr ⟨w, hws, hw⟩
  · rw [if_neg hw]

/-- Every actual quotient element is a finite sum of actual homogeneous
elements, with zero terms outside the same actual finite degree support. -/
theorem exists_finite_homogeneous_decomposition
    (I : TwoSidedIdeal (WordAlgebra F)) (b : WordIdealQuotient F I) :
    ∃ (S : Finset ℕ) (x : ℕ → WordIdealQuotient F I),
      (∀ n, x n ∈ degreeSpace F I n) ∧
      (∀ n, n ∉ S → x n = 0) ∧ (∑ n ∈ S, x n) = b := by
  classical
  obtain ⟨P, rfl⟩ := wordIdealQuotientMap_surjective F I b
  let x : ℕ → WordIdealQuotient F I :=
    fun n => wordIdealQuotientMap F I (homogeneousProjection F n P).val
  refine ⟨wordDegreeSupport F P, x, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(homogeneousProjection F n P).val,
      (homogeneousProjection F n P).property, rfl⟩
  · intro n hn
    change wordIdealQuotientMap F I (homogeneousProjection F n P).val = 0
    rw [homogeneousProjection_eq_zero_of_not_mem_degreeSupport F P n hn, map_zero]
  · change (∑ n ∈ wordDegreeSupport F P,
      wordIdealQuotientMap F I (homogeneousProjection F n P).val) = wordIdealQuotientMap F I P
    rw [← map_sum, sum_homogeneousProjection_eq]

/-- Actual projection isolation proves directness for every finite degree set,
including degree zero. -/
theorem homogeneous_finite_sum_eq_zero_imp_terms_eq_zero
    (I : TwoSidedIdeal (WordAlgebra F)) (hhom : WordIdealHomogeneous F I)
    (S : Finset ℕ) (x : ℕ → WordIdealQuotient F I)
    (hx : ∀ n, x n ∈ degreeSpace F I n) (hzero : (∑ n ∈ S, x n) = 0) :
    ∀ n, n ∈ S → x n = 0 := by
  classical
  have hex : ∀ n : ℕ, ∃ y : WordAlgebra F,
      y ∈ homogeneous F n ∧ wordIdealQuotientMap F I y = x n := fun n =>
    Submodule.mem_map.mp (hx n)
  choose y hy hq using hex
  have hI : (∑ n ∈ S, y n) ∈ I := by
    apply (wordIdealQuotientMap_eq_zero_iff F I _).mp
    rw [map_sum]
    simpa only [hq] using hzero
  intro n hn
  let p : WordAlgebra F →ₗ[F] WordAlgebra F :=
    (homogeneous F n).subtype.comp (homogeneousProjection F n)
  have hp : ∀ m : ℕ, p (y m) = if m = n then y n else 0 := by
    intro m
    by_cases hmn : m = n
    · subst m
      simp only [p, LinearMap.comp_apply, Submodule.subtype_apply,
        homogeneousProjection_of_mem F n (y n) (hy n), ite_true]
    · simp only [p, LinearMap.comp_apply, Submodule.subtype_apply,
        homogeneousProjection_of_other_degree F m n hmn (y m) (hy m), if_neg hmn]
  have hproject : (homogeneousProjection F n (∑ m ∈ S, y m)).val = y n := by
    change p (∑ m ∈ S, y m) = _
    rw [map_sum]
    simp only [hp]
    rw [Finset.sum_eq_single n]
    · simp
    · intro m _ hmn
      simp [hmn]
    · intro hn'
      exact False.elim (hn' hn)
  have hynI := hhom n _ hI
  rw [hproject] at hynI
  rw [← hq n]
  exact (wordIdealQuotientMap_eq_zero_iff F I _).mpr hynI

/-- The actual degree spaces span the entire literal quotient. -/
theorem degreeSpace_iSup_eq_top (I : TwoSidedIdeal (WordAlgebra F)) :
    (⨆ n : ℕ, degreeSpace F I n) = ⊤ := by
  apply eq_top_iff.mpr
  intro b _
  obtain ⟨S, x, hx, _, hsum⟩ := exists_finite_homogeneous_decomposition F I b
  rw [← hsum]
  apply Submodule.sum_mem
  intro n _
  exact (le_iSup (degreeSpace F I) n) (hx n)

/-- Canonical linear map from the literal direct sum of the actual degree spaces. -/
def degreeDirectSumMap (I : TwoSidedIdeal (WordAlgebra F)) :
    (⨁ n : ℕ, degreeSpace F I n) →ₗ[F] WordIdealQuotient F I :=
  DirectSum.coeLinearMap (degreeSpace F I)

theorem degreeDirectSumMap_eq_zero_iff
    (I : TwoSidedIdeal (WordAlgebra F)) (hhom : WordIdealHomogeneous F I)
    (x : ⨁ n : ℕ, degreeSpace F I n) :
    degreeDirectSumMap F I x = 0 ↔ ∀ n, x n = 0 := by
  classical
  constructor
  · intro hz
    have hsum : (∑ n ∈ x.support, (x n).val) = 0 := by
      change DirectSum.coeLinearMap (degreeSpace F I) x = 0 at hz
      simpa only [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum] using hz
    have hterms := homogeneous_finite_sum_eq_zero_imp_terms_eq_zero F I hhom
      x.support (fun n => (x n).val) (fun n => (x n).property) hsum
    intro n
    by_cases hn : n ∈ x.support
    · apply Subtype.ext
      exact hterms n hn
    · exact DFinsupp.notMem_support_iff.mp hn
  · intro hx
    let z : Π₀ n : ℕ, degreeSpace F I n :=
      ⟨fun _ => 0, Trunc.mk ⟨∅, fun _ => Or.inr rfl⟩⟩
    have heq : x = z := DFinsupp.ext hx
    rw [heq]
    exact (degreeDirectSumMap F I).map_zero

theorem degreeDirectSumMap_injective
    (I : TwoSidedIdeal (WordAlgebra F)) (hhom : WordIdealHomogeneous F I) :
    Function.Injective (degreeDirectSumMap F I) := by
  intro x y he
  have hz : degreeDirectSumMap F I (x - y) = 0 := by
    rw [(degreeDirectSumMap F I).map_sub, he, sub_self]
  have hterms := (degreeDirectSumMap_eq_zero_iff F I hhom _).mp hz
  apply DFinsupp.ext
  intro n
  apply sub_eq_zero.mp
  simpa only [DFinsupp.sub_apply] using hterms n

/-- A genuine internal direct-sum decomposition of the actual quotient. -/
theorem degreeSpace_isInternal
    (I : TwoSidedIdeal (WordAlgebra F)) (hhom : WordIdealHomogeneous F I) :
    DirectSum.IsInternal (degreeSpace F I) := by
  refine ⟨degreeDirectSumMap_injective F I hhom, ?_⟩
  change Function.Surjective (degreeDirectSumMap F I)
  apply LinearMap.range_eq_top.mp
  change LinearMap.range (DirectSum.coeLinearMap (degreeSpace F I)) = ⊤
  rw [DirectSum.range_coeLinearMap, degreeSpace_iSup_eq_top]

/-- Actual multiplication of quotient homogeneous elements adds word degrees. -/
theorem degreeSpace_mul_mem
    (I : TwoSidedIdeal (WordAlgebra F)) (a b : ℕ)
    (x y : WordIdealQuotient F I)
    (hx : x ∈ degreeSpace F I a) (hy : y ∈ degreeSpace F I b) :
    x * y ∈ degreeSpace F I (a + b) := by
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨Q, hQ, rfl⟩ := Submodule.mem_map.mp hy
  exact ⟨P * Q, homogeneous_mul F hP hQ,
    (wordIdealQuotientMap F I).map_mul P Q⟩

theorem one_mem_degreeSpace_zero (I : TwoSidedIdeal (WordAlgebra F)) :
    (1 : WordIdealQuotient F I) ∈ degreeSpace F I 0 := by
  have hword : (1 : WordAlgebra F) ∈ homogeneous F 0 := by
    simpa only [MonoidAlgebra.one_def] using monomial_mem_homogeneous F 0
      ⟨(1 : Word), rfl⟩ (1 : F)
  exact ⟨1, hword, (wordIdealQuotientMap F I).map_one⟩

#print axioms CriticalGK2.HomogeneousGrading.exists_finite_homogeneous_decomposition
#print axioms CriticalGK2.HomogeneousGrading.degreeSpace_isInternal
#print axioms CriticalGK2.HomogeneousGrading.degreeSpace_mul_mem

end

end CriticalGK2.HomogeneousGrading
