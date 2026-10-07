import CriticalGK2.PositiveWordIdealGrowth
import CriticalGK2.GenericHomogeneousGrading

/-!
# Actual positive grading of the actual further quotient

The index m names actual word degree m+1. The spaces are exactly the
`positiveIdealDegreeSpace` submodules defined for the actual positive
augmentation kernel. They form an internal direct sum and their products
lie in the space indexed by m+n+1. Thus every actual positive element has a
unique finite decomposition in strictly positive word degrees.
-/

namespace CriticalGK2.Actual

noncomputable section

open scoped BigOperators DirectSum

variable (F : Type*) [Field F]
variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)

/-- The literal positive image of a homogeneous free-word element. -/
def homogeneousToPositiveIdeal (n : ℕ) (hn : n ≠ 0) :
    homogeneous F n →ₗ[F] PositiveWordIdealQuotient F I hpos where
  toFun P := positiveWordIdealQuotientMap F I hpos
    ⟨P.val, augmentation_homogeneous_eq_zero F n hn P.val P.property⟩
  map_add' P Q := Subtype.ext ((wordIdealQuotientMap F I).map_add P.val Q.val)
  map_smul' c P := Subtype.ext ((wordIdealQuotientMap F I).toLinearMap.map_smul c P.val)

@[simp]
theorem homogeneousToPositiveIdeal_val (n : ℕ) (hn : n ≠ 0) (P : homogeneous F n) :
    (homogeneousToPositiveIdeal F I hpos n hn P).val = wordIdealQuotientMap F I P.val := rfl

/-- The actual degree space is exactly the range of the same-degree word map. -/
theorem positiveIdealDegreeSpace_eq_range (m : ℕ) :
    positiveIdealDegreeSpace F I hpos m =
      LinearMap.range (homogeneousToPositiveIdeal F I hpos (m + 1) (by omega)) := by
  ext a
  constructor
  · intro ha
    change a.val ∈ idealDegreeSpace F I (m + 1) at ha
    obtain ⟨P, hP, hPa⟩ := Submodule.mem_map.mp ha
    exact ⟨⟨P, hP⟩, Subtype.ext hPa⟩
  · rintro ⟨P, rfl⟩
    change wordIdealQuotientMap F I P.val ∈ idealDegreeSpace F I (m + 1)
    exact ⟨P.val, P.property, rfl⟩

instance positiveIdealDegreeSpace_finite (m : ℕ) :
    FiniteDimensional F (positiveIdealDegreeSpace F I hpos m) := by
  rw [positiveIdealDegreeSpace_eq_range]
  letI : FiniteDimensional F (homogeneous F (m + 1)) :=
    (homogeneousWordBasis F (m + 1)).finiteDimensional_of_finite
  exact Module.Finite.range (homogeneousToPositiveIdeal F I hpos (m + 1) (by omega))

theorem zero_not_mem_positive_wordDegreeSupport (P : positiveWordSubmodule F) :
    0 ∉ wordDegreeSupport F P.val := by
  classical
  intro hzero
  obtain ⟨w, hw, hlen⟩ := Finset.mem_image.mp hzero
  have hwone : w = 1 := FreeMonoid.length_eq_zero.mp hlen
  subst w
  have hP : P.val 1 = 0 := (augmentation_eq_constantCoeff F P.val).symm.trans P.property
  exact (Finsupp.mem_support_iff.mp hw) hP

/-- Every positive quotient element has a genuine finite positive-degree
decomposition; the original degree support is reindexed by degree minus one. -/
theorem exists_positiveIdeal_finite_homogeneous_decomposition
    (a : PositiveWordIdealQuotient F I hpos) :
    ∃ (S : Finset ℕ) (x : ℕ → PositiveWordIdealQuotient F I hpos),
      (∀ m, x m ∈ positiveIdealDegreeSpace F I hpos m) ∧
      (∀ m, m ∉ S → x m = 0) ∧ (∑ m ∈ S, x m) = a := by
  classical
  obtain ⟨P, hPa⟩ := positiveWordIdealQuotientMap_surjective F I hpos a
  let x : ℕ → PositiveWordIdealQuotient F I hpos := fun m =>
    homogeneousToPositiveIdeal F I hpos (m + 1) (by omega)
      (homogeneousProjection F (m + 1) P.val)
  have hpositive (n : ℕ) (hn : n ∈ wordDegreeSupport F P.val) : 0 < n := by
    have hne : n ≠ 0 := fun h => zero_not_mem_positive_wordDegreeSupport F P (h ▸ hn)
    omega
  refine ⟨(wordDegreeSupport F P.val).image (fun n => n - 1), x, ?_, ?_, ?_⟩
  · intro m
    rw [positiveIdealDegreeSpace_eq_range]
    exact ⟨homogeneousProjection F (m + 1) P.val, rfl⟩
  · intro m hm
    have hnot : m + 1 ∉ wordDegreeSupport F P.val := by
      intro hmem
      apply hm
      exact Finset.mem_image.mpr ⟨m + 1, hmem, by omega⟩
    apply Subtype.ext
    change wordIdealQuotientMap F I (homogeneousProjection F (m + 1) P.val).val = 0
    rw [CriticalGK2.HomogeneousGrading.homogeneousProjection_eq_zero_of_not_mem_degreeSupport
      F P.val (m + 1) hnot, map_zero]
  · apply Subtype.ext
    change positiveWordIdealLinearInclusion F I hpos
      (∑ m ∈ (wordDegreeSupport F P.val).image (fun n => n - 1), x m) =
      positiveWordIdealLinearInclusion F I hpos a
    rw [map_sum]
    change (∑ m ∈ (wordDegreeSupport F P.val).image (fun n => n - 1), (x m).val) = a.val
    rw [Finset.sum_image]
    · calc
        (∑ n ∈ wordDegreeSupport F P.val, (x (n - 1)).val) =
            ∑ n ∈ wordDegreeSupport F P.val,
              wordIdealQuotientMap F I (homogeneousProjection F n P.val).val := by
          apply Finset.sum_congr rfl
          intro n hn
          have hdegree : n - 1 + 1 = n := by have := hpositive n hn; omega
          change wordIdealQuotientMap F I (homogeneousProjection F (n - 1 + 1) P.val).val = _
          rw [hdegree]
        _ = wordIdealQuotientMap F I P.val := by rw [← map_sum, sum_homogeneousProjection_eq]
        _ = a.val := congrArg (fun a : PositiveWordIdealQuotient F I hpos => a.val) hPa
    · intro n hn k hk hnk
      have := hpositive n hn
      have := hpositive k hk
      change n - 1 = k - 1 at hnk
      omega

/-- Projection isolation for an arbitrary finite family of actual positive degrees. -/
theorem positiveIdeal_finite_sum_eq_zero_imp_terms_eq_zero
    (hhom : WordIdealHomogeneous F I) (S : Finset ℕ)
    (x : ℕ → PositiveWordIdealQuotient F I hpos)
    (hx : ∀ m, x m ∈ positiveIdealDegreeSpace F I hpos m)
    (hzero : (∑ m ∈ S, x m) = 0) : ∀ m, m ∈ S → x m = 0 := by
  classical
  have hex : ∀ m : ℕ, ∃ P : WordAlgebra F,
      P ∈ homogeneous F (m + 1) ∧ wordIdealQuotientMap F I P = (x m).val :=
    fun m => Submodule.mem_map.mp
      (show (x m).val ∈ idealDegreeSpace F I (m + 1) from hx m)
  choose P hP hq using hex
  have hI : (∑ m ∈ S, P m) ∈ I := by
    apply (wordIdealQuotientMap_eq_zero_iff F I _).mp
    rw [map_sum]
    have hval := congrArg (positiveWordIdealLinearInclusion F I hpos) hzero
    rw [map_sum, map_zero] at hval
    simpa only [hq] using hval
  intro m hm
  let p : WordAlgebra F →ₗ[F] WordAlgebra F :=
    (homogeneous F (m + 1)).subtype.comp (homogeneousProjection F (m + 1))
  have hp (n : ℕ) : p (P n) = if n = m then P m else 0 := by
    by_cases hnm : n = m
    · subst n
      simp only [p, LinearMap.comp_apply, Submodule.subtype_apply,
        homogeneousProjection_of_mem F (m + 1) (P m) (hP m), ite_true]
    · have hdegree : n + 1 ≠ m + 1 := by omega
      simp only [p, LinearMap.comp_apply, Submodule.subtype_apply,
        homogeneousProjection_of_other_degree F (n + 1) (m + 1) hdegree (P n) (hP n), if_neg hnm]
  have hproject : (homogeneousProjection F (m + 1) (∑ n ∈ S, P n)).val = P m := by
    change p (∑ n ∈ S, P n) = _
    rw [map_sum]
    simp only [hp]
    rw [Finset.sum_eq_single m]
    · simp
    · intro n _ hnm
      simp [hnm]
    · intro hm'
      exact False.elim (hm' hm)
  have hPmI := hhom (m + 1) _ hI
  rw [hproject] at hPmI
  apply Subtype.ext
  rw [← hq m]
  exact (wordIdealQuotientMap_eq_zero_iff F I _).mpr hPmI

theorem positiveIdealDegreeSpace_iSup_eq_top :
    (⨆ m : ℕ, positiveIdealDegreeSpace F I hpos m) = ⊤ := by
  apply eq_top_iff.mpr
  intro a _
  obtain ⟨S, x, hx, _, hsum⟩ := exists_positiveIdeal_finite_homogeneous_decomposition F I hpos a
  rw [← hsum]
  apply Submodule.sum_mem
  intro m _
  exact (le_iSup (positiveIdealDegreeSpace F I hpos) m) (hx m)

def positiveIdealDegreeDirectSumMap :
    (⨁ m : ℕ, positiveIdealDegreeSpace F I hpos m) →ₗ[F] PositiveWordIdealQuotient F I hpos :=
  DirectSum.coeLinearMap (positiveIdealDegreeSpace F I hpos)

theorem positiveIdealDegreeDirectSumMap_injective (hhom : WordIdealHomogeneous F I) :
    Function.Injective (positiveIdealDegreeDirectSumMap F I hpos) := by
  classical
  intro x y he
  let z := x - y
  have hsum : (∑ m ∈ z.support, (z m).val) = 0 := by
    have hz : positiveIdealDegreeDirectSumMap F I hpos z = 0 := by
      dsimp only [z]
      rw [(positiveIdealDegreeDirectSumMap F I hpos).map_sub, he, sub_self]
    change DirectSum.coeLinearMap (positiveIdealDegreeSpace F I hpos) z = 0 at hz
    simpa only [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum] using hz
  have hterms := positiveIdeal_finite_sum_eq_zero_imp_terms_eq_zero F I hpos hhom
    z.support (fun m => (z m).val) (fun m => (z m).property) hsum
  apply DFinsupp.ext
  intro m
  have hzm : z m = 0 := by
    by_cases hm : m ∈ z.support
    · exact Subtype.ext (hterms m hm)
    · exact DFinsupp.notMem_support_iff.mp hm
  apply sub_eq_zero.mp
  simpa only [z, DFinsupp.sub_apply] using hzm

/-- The actual positive quotient is the internal direct sum of actual degrees m+1. -/
theorem positiveIdealDegreeSpace_isInternal (hhom : WordIdealHomogeneous F I) :
    DirectSum.IsInternal (positiveIdealDegreeSpace F I hpos) := by
  refine ⟨positiveIdealDegreeDirectSumMap_injective F I hpos hhom, ?_⟩
  change Function.Surjective (positiveIdealDegreeDirectSumMap F I hpos)
  apply LinearMap.range_eq_top.mp
  change LinearMap.range (DirectSum.coeLinearMap (positiveIdealDegreeSpace F I hpos)) = ⊤
  rw [DirectSum.range_coeLinearMap, positiveIdealDegreeSpace_iSup_eq_top]

/-- With index m denoting degree m+1, actual multiplication has index m+n+1. -/
theorem positiveIdealDegreeSpace_mul_mem (m n : ℕ)
    (x y : PositiveWordIdealQuotient F I hpos)
    (hx : x ∈ positiveIdealDegreeSpace F I hpos m)
    (hy : y ∈ positiveIdealDegreeSpace F I hpos n) :
    x * y ∈ positiveIdealDegreeSpace F I hpos (m + n + 1) := by
  have hmul := CriticalGK2.HomogeneousGrading.degreeSpace_mul_mem F I (m + 1) (n + 1)
    x.val y.val hx hy
  change x.val * y.val ∈ CriticalGK2.HomogeneousGrading.degreeSpace F I ((m + n + 1) + 1)
  have hdegree : (m + 1) + (n + 1) = (m + n + 1) + 1 := by omega
  rw [hdegree] at hmul
  exact hmul

#print axioms CriticalGK2.Actual.exists_positiveIdeal_finite_homogeneous_decomposition
#print axioms CriticalGK2.Actual.positiveIdealDegreeSpace_isInternal
#print axioms CriticalGK2.Actual.positiveIdealDegreeSpace_mul_mem

end

end CriticalGK2.Actual
