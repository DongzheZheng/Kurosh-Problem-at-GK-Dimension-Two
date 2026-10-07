import CriticalGK2.HomogeneousIdealZorn
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Literal homogeneous ideal quotients and actual word tails

For an arbitrary actual ideal I, inclusion of a word tail gives a literal
finite-dimensional ring quotient. Conversely, for a homogeneous I, a finite
basis of the quotient can be lifted to actual finite word polynomials. A
single cutoff then bounds all chosen lifts. Actual degree projection shows
that every sufficiently long monomial is in I.

Thus the no-tail conclusion of the Zorn theorem implies
infinite-dimensionality of H/I.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- Literal quotient by an arbitrary literal ideal of the free word algebra. -/
abbrev WordIdealQuotient (I : TwoSidedIdeal (WordAlgebra F)) := I.ringCon.Quotient

def wordIdealQuotientMap (I : TwoSidedIdeal (WordAlgebra F)) :
    WordAlgebra F →ₐ[F] WordIdealQuotient F I := I.ringCon.mkₐ F

theorem wordIdealQuotientMap_surjective (I : TwoSidedIdeal (WordAlgebra F)) :
    Function.Surjective (wordIdealQuotientMap F I) := RingCon.mkₐ_surjective I.ringCon

@[simp]
theorem wordIdealQuotientMap_eq_zero_iff (I : TwoSidedIdeal (WordAlgebra F))
    (P : WordAlgebra F) : wordIdealQuotientMap F I P = 0 ↔ P ∈ I := by
  change I.ringCon.mk' P = 0 ↔ _
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

/-- A tail inclusion gives an actual surjection from actual short words. -/
theorem wordIdealQuotient_short_surjective_of_tail
    (I : TwoSidedIdeal (WordAlgebra F)) (N : ℕ) (hN : wordTailIdeal F N ≤ I) :
    Function.Surjective ((wordIdealQuotientMap F I).toLinearMap.comp
      (shortWordSubmodule F N).subtype) := by
  intro x
  obtain ⟨P, rfl⟩ := wordIdealQuotientMap_surjective F I x
  refine ⟨shortWordProjection F N P, ?_⟩
  change wordIdealQuotientMap F I (shortWordProjection F N P).val = wordIdealQuotientMap F I P
  apply Eq.symm
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (wordIdealQuotientMap_eq_zero_iff F I _).mpr
  exact hN ((mem_wordTailIdeal F N _).mpr (sub_shortWordProjection_mem_tail F N P))

theorem wordIdealQuotient_finite_of_tail (I : TwoSidedIdeal (WordAlgebra F))
    (N : ℕ) (hN : wordTailIdeal F N ≤ I) : Module.Finite F (WordIdealQuotient F I) :=
  FiniteDimensional.of_surjective
    ((wordIdealQuotientMap F I).toLinearMap.comp (shortWordSubmodule F N).subtype)
    (wordIdealQuotient_short_surjective_of_tail F I N hN)

/-- A finite-dimensional literal quotient has representatives in a single
actual short-word subspace, proved by lifting an actual finite basis. -/
theorem wordIdealQuotient_exists_short_surjective
    (I : TwoSidedIdeal (WordAlgebra F)) (hfinite : Module.Finite F (WordIdealQuotient F I)) :
    ∃ N : ℕ, Function.Surjective ((wordIdealQuotientMap F I).toLinearMap.comp
      (shortWordSubmodule F N).subtype) := by
  classical
  letI : Module.Finite F (WordIdealQuotient F I) := hfinite
  let b := Module.finBasis F (WordIdealQuotient F I)
  let P : Fin (Module.finrank F (WordIdealQuotient F I)) → WordAlgebra F :=
    fun i => Classical.choose (wordIdealQuotientMap_surjective F I (b i))
  have hP : ∀ i, wordIdealQuotientMap F I (P i) = b i :=
    fun i => Classical.choose_spec (wordIdealQuotientMap_surjective F I (b i))
  let D : ℕ := Finset.univ.sup (fun i =>
    (MonoidAlgebra.coeff (P i)).support.sup (fun w : Word => w.length))
  have hshort : ∀ i, P i ∈ shortWordSubmodule F (D + 1) := by
    intro i
    change ∀ w ∈ (MonoidAlgebra.coeff (P i)).support, w.length < D + 1
    intro w hw
    have hlocal : w.length ≤
        (MonoidAlgebra.coeff (P i)).support.sup (fun w : Word => w.length) :=
      Finset.le_sup hw
    have hall : (MonoidAlgebra.coeff (P i)).support.sup (fun w : Word => w.length) ≤ D := by
      exact Finset.le_sup (f := fun i =>
        (MonoidAlgebra.coeff (P i)).support.sup (fun w : Word => w.length)) (Finset.mem_univ i)
    exact Nat.lt_succ_of_le (hlocal.trans hall)
  refine ⟨D + 1, ?_⟩
  intro x
  let Q : Fin (Module.finrank F (WordIdealQuotient F I)) → shortWordSubmodule F (D + 1) :=
    fun i => ⟨P i, hshort i⟩
  refine ⟨∑ i, b.repr x i • Q i, ?_⟩
  rw [map_sum]
  simp only [map_smul, LinearMap.comp_apply, Submodule.subtype_apply]
  change (∑ i, b.repr x i • wordIdealQuotientMap F I (P i)) = x
  simp only [hP]
  exact b.sum_repr x

/-- Projection to a degree at least N kills an actual short polynomial. -/
theorem homogeneousProjection_short_eq_zero (N n : ℕ) (hNn : N ≤ n)
    (P : WordAlgebra F) (hP : P ∈ shortWordSubmodule F N) :
    (homogeneousProjection F n P).val = 0 := by
  apply Finsupp.ext
  intro w
  change (homogeneousProjection F n P).val w = (0 : F)
  rw [homogeneousProjection_coeff]
  by_cases hw : w.length = n
  · rw [if_pos hw]
    have hnot : ¬ w.length < N := by omega
    exact (Finsupp.mem_supported' (s := {w : Word | w.length < N}) F P).mp hP w hnot
  · rw [if_neg hw]

/-- Homogeneity plus actual short representatives forces an actual word tail. -/
theorem wordTailIdeal_le_of_short_surjective
    (I : TwoSidedIdeal (WordAlgebra F)) (hhom : WordIdealHomogeneous F I)
    (N : ℕ) (hsurj : Function.Surjective ((wordIdealQuotientMap F I).toLinearMap.comp
      (shortWordSubmodule F N).subtype)) : wordTailIdeal F N ≤ I := by
  apply wordTailIdeal_le_of_length_monomials F I N
  intro w
  let M : WordAlgebra F := MonoidAlgebra.single w.val 1
  have hM : M ∈ homogeneous F N := monomial_mem_homogeneous F N w 1
  obtain ⟨P, hP⟩ := hsurj (wordIdealQuotientMap F I M)
  have hdiff : M - P.val ∈ I := by
    apply (wordIdealQuotientMap_eq_zero_iff F I _).mp
    rw [map_sub]
    exact sub_eq_zero.mpr hP.symm
  have hproj := hhom N (M - P.val) hdiff
  have heq : (homogeneousProjection F N (M - P.val)).val = M := by
    rw [map_sub]
    change (homogeneousProjection F N M).val - (homogeneousProjection F N P.val).val = M
    rw [homogeneousProjection_of_mem F N M hM,
      homogeneousProjection_short_eq_zero F N N le_rfl P.val P.property, sub_zero]
  rw [heq] at hproj
  exact hproj

theorem wordIdealQuotient_finite_iff_tail (I : TwoSidedIdeal (WordAlgebra F))
    (hhom : WordIdealHomogeneous F I) :
    Module.Finite F (WordIdealQuotient F I) ↔ ∃ N : ℕ, wordTailIdeal F N ≤ I := by
  constructor
  · intro hfinite
    obtain ⟨N, hN⟩ := wordIdealQuotient_exists_short_surjective F I hfinite
    exact ⟨N, wordTailIdeal_le_of_short_surjective F I hhom N hN⟩
  · rintro ⟨N, hN⟩
    exact wordIdealQuotient_finite_of_tail F I N hN

/-- A homogeneous ideal containing no word tail has an infinite-dimensional
ring quotient. -/
theorem wordIdealQuotient_not_finite_of_noWordTail (I : TwoSidedIdeal (WordAlgebra F))
    (hhom : WordIdealHomogeneous F I) (htail : NoWordTail F I) :
    ¬ Module.Finite F (WordIdealQuotient F I) := by
  intro hfinite
  obtain ⟨N, hN⟩ := (wordIdealQuotient_finite_iff_tail F I hhom).mp hfinite
  exact htail N hN

/-- Maximal homogeneous no-tail extensions give a genuine infinite quotient
and finite-dimensional quotients at every strict homogeneous extension. -/
theorem exists_homogeneous_ideal_infinite_with_finite_strict_quotients
    (I₀ : TwoSidedIdeal (WordAlgebra F))
    (hhom₀ : WordIdealHomogeneous F I₀) (htail₀ : NoWordTail F I₀) :
    ∃ I : TwoSidedIdeal (WordAlgebra F), I₀ ≤ I ∧ WordIdealHomogeneous F I ∧
      ¬ Module.Finite F (WordIdealQuotient F I) ∧
      ∀ J : TwoSidedIdeal (WordAlgebra F), WordIdealHomogeneous F J → I < J →
        Module.Finite F (WordIdealQuotient F J) := by
  obtain ⟨I, hle, hhom, htail, hmax⟩ :=
    exists_maximal_homogeneous_noWordTail F I₀ hhom₀ htail₀
  refine ⟨I, hle, hhom, wordIdealQuotient_not_finite_of_noWordTail F I hhom htail, ?_⟩
  intro J hhomJ hIJ
  obtain ⟨N, hN⟩ := hmax J hhomJ hIJ
  exact wordIdealQuotient_finite_of_tail F J N hN

#print axioms CriticalGK2.Actual.wordIdealQuotient_exists_short_surjective
#print axioms CriticalGK2.Actual.wordIdealQuotient_finite_iff_tail
#print axioms CriticalGK2.Actual.wordIdealQuotient_not_finite_of_noWordTail
#print axioms CriticalGK2.Actual.exists_homogeneous_ideal_infinite_with_finite_strict_quotients

end

end CriticalGK2.Actual
