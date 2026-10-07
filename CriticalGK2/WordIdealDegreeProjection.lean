import CriticalGK2.LeadingDegree
import CriticalGK2.GenericHomogeneousGrading

/-!
# Actual homogeneous projections on a homogeneous word-ideal quotient

The projections are descended from literal coefficient-degree projections
on the free word algebra. Equality of two quotient representatives implies
equality of their projected representatives by the homogeneity of the
ideal. The projections are therefore independent of the chosen
representatives.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]
variable (I : TwoSidedIdeal (WordAlgebra F))

theorem wordIdealQuotient_project_eq_of_map_eq
    (hhom : WordIdealHomogeneous F I) (n : ℕ) (P Q : WordAlgebra F)
    (hPQ : wordIdealQuotientMap F I P = wordIdealQuotientMap F I Q) :
    wordIdealQuotientMap F I (degreeProjection F n P) =
      wordIdealQuotientMap F I (degreeProjection F n Q) := by
  have hdifference : P - Q ∈ I := by
    apply (wordIdealQuotientMap_eq_zero_iff F I _).mp
    rw [map_sub, hPQ, sub_self]
  have hproject := hhom n (P - Q) hdifference
  apply sub_eq_zero.mp
  rw [← map_sub, ← (degreeProjection F n).map_sub]
  exact (wordIdealQuotientMap_eq_zero_iff F I _).mpr hproject

def wordIdealDegreeProjectionFun (n : ℕ) (b : WordIdealQuotient F I) :
    WordIdealQuotient F I :=
  wordIdealQuotientMap F I (degreeProjection F n
    (Classical.choose (wordIdealQuotientMap_surjective F I b)))

theorem wordIdealDegreeProjectionFun_map (hhom : WordIdealHomogeneous F I)
    (n : ℕ) (P : WordAlgebra F) :
    wordIdealDegreeProjectionFun F I n (wordIdealQuotientMap F I P) =
      wordIdealQuotientMap F I (degreeProjection F n P) := by
  apply wordIdealQuotient_project_eq_of_map_eq F I hhom n
  exact Classical.choose_spec (wordIdealQuotientMap_surjective F I
    (wordIdealQuotientMap F I P))

/-- The actual F-linear degree projection on the literal ring quotient. -/
def wordIdealDegreeProjection (hhom : WordIdealHomogeneous F I) (n : ℕ) :
    WordIdealQuotient F I →ₗ[F] WordIdealQuotient F I where
  toFun := wordIdealDegreeProjectionFun F I n
  map_add' x y := by
    obtain ⟨P, rfl⟩ := wordIdealQuotientMap_surjective F I x
    obtain ⟨Q, rfl⟩ := wordIdealQuotientMap_surjective F I y
    rw [← map_add, wordIdealDegreeProjectionFun_map F I hhom,
      wordIdealDegreeProjectionFun_map F I hhom,
      wordIdealDegreeProjectionFun_map F I hhom, map_add, map_add]
  map_smul' c x := by
    obtain ⟨P, rfl⟩ := wordIdealQuotientMap_surjective F I x
    rw [← map_smul, wordIdealDegreeProjectionFun_map F I hhom,
      wordIdealDegreeProjectionFun_map F I hhom, map_smul, map_smul]
    simp only [RingHom.id_apply]

@[simp]
theorem wordIdealDegreeProjection_map (hhom : WordIdealHomogeneous F I)
    (n : ℕ) (P : WordAlgebra F) :
    wordIdealDegreeProjection F I hhom n (wordIdealQuotientMap F I P) =
      wordIdealQuotientMap F I (degreeProjection F n P) :=
  wordIdealDegreeProjectionFun_map F I hhom n P

/-- Actual degree-space elements have the literal delta projection law. -/
theorem wordIdealDegreeProjection_of_degreeSpace
    (hhom : WordIdealHomogeneous F I) (m n : ℕ)
    (b : WordIdealQuotient F I)
    (hb : b ∈ CriticalGK2.HomogeneousGrading.degreeSpace F I n) :
    wordIdealDegreeProjection F I hhom m b = if n = m then b else 0 := by
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.mp hb
  change wordIdealDegreeProjection F I hhom m (wordIdealQuotientMap F I P) =
    if n = m then wordIdealQuotientMap F I P else 0
  rw [wordIdealDegreeProjection_map]
  by_cases hnm : n = m
  · subst n
    rw [if_pos rfl, degreeProjection_of_mem F m P hP]
  · rw [if_neg hnm, degreeProjection_of_other_degree F n m hnm P hP, map_zero]

#print axioms CriticalGK2.Actual.wordIdealDegreeProjection_map
#print axioms CriticalGK2.Actual.wordIdealDegreeProjection_of_degreeSpace

end

end CriticalGK2.Actual
