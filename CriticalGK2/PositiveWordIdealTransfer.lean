import CriticalGK2.PositiveWordIdealQuotient
import CriticalGK2.GenericPositivePrime
import CriticalGK2.GenericResidualFinite
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual maps and ordinary properties of the new positive quotient

The factor map is a genuine non-unital algebra homomorphism from the
original positive all-cut quotient to the new positive H-plus/I. It is
proved surjective by actual H-plus representatives.

The same literal positive quotient inherits ordinary primeness via the
proved scalar-plus-positive decomposition, infinitude via a surjective
F-linear scalar-plus-positive map, and residual finite dimensionality via
the actual subtype inclusion and literal finite tail quotients.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]
variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)

theorem wordIdealFactor_augmentation (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (hEI : allCutTwoSidedIdeal F W hW ≤ I) (b : AllCutRingQuotient F W hW) :
    wordIdealQuotientAugmentation F I hpos (wordIdealFactorFromAllCut F W hW I hEI b) =
      allCutQuotientAugmentation F W hW b := by
  obtain ⟨P, rfl⟩ := allCutQuotientMap_surjective F W hW b
  rfl

/-- Actual positive further-quotient map, with ordinary inherited operations. -/
def positiveWordIdealFactor (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (hEI : allCutTwoSidedIdeal F W hW ≤ I) :
    PositiveAllCutQuotient F W hW →ₙₐ[F] PositiveWordIdealQuotient F I hpos where
  toFun a := ⟨wordIdealFactorFromAllCut F W hW I hEI a.val, by
    change wordIdealQuotientAugmentation F I hpos
      (wordIdealFactorFromAllCut F W hW I hEI a.val) = 0
    rw [wordIdealFactor_augmentation F I hpos W hW hEI]
    exact a.property⟩
  map_zero' := Subtype.ext (wordIdealFactorFromAllCut F W hW I hEI).map_zero
  map_add' a b := Subtype.ext ((wordIdealFactorFromAllCut F W hW I hEI).map_add a.val b.val)
  map_mul' a b := Subtype.ext ((wordIdealFactorFromAllCut F W hW I hEI).map_mul a.val b.val)
  map_smul' c a := Subtype.ext ((wordIdealFactorFromAllCut F W hW I hEI).toLinearMap.map_smul c a.val)

@[simp]
theorem positiveWordIdealFactor_val (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (hEI : allCutTwoSidedIdeal F W hW ≤ I) (a : PositiveAllCutQuotient F W hW) :
    (positiveWordIdealFactor F I hpos W hW hEI a).val =
      wordIdealFactorFromAllCut F W hW I hEI a.val := rfl

theorem positiveWordIdealFactor_surjective (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (hEI : allCutTwoSidedIdeal F W hW ≤ I) :
    Function.Surjective (positiveWordIdealFactor F I hpos W hW hEI) := by
  intro a
  obtain ⟨P, hP⟩ := positiveWordIdealQuotientMap_surjective F I hpos a
  refine ⟨positiveAllCutQuotientMap F W hW P, ?_⟩
  apply Subtype.ext
  change wordIdealFactorFromAllCut F W hW I hEI (allCutQuotientMap F W hW P.val) = a.val
  rw [wordIdealFactorFromAllCut_map]
  exact congrArg (fun a : PositiveWordIdealQuotient F I hpos => a.val) hP

def scalarPlusPositiveLinearMap :
    F × PositiveWordIdealQuotient F I hpos →ₗ[F] WordIdealQuotient F I :=
  (LinearMap.toSpanSingleton F (WordIdealQuotient F I) 1).comp
      (LinearMap.fst F F (PositiveWordIdealQuotient F I hpos)) +
    (positiveWordIdealLinearInclusion F I hpos).comp
      (LinearMap.snd F F (PositiveWordIdealQuotient F I hpos))

theorem scalarPlusPositiveLinearMap_surjective :
    Function.Surjective (scalarPlusPositiveLinearMap F I hpos) := by
  intro b
  obtain ⟨c, a, hb⟩ := positiveWordIdeal_scalar_split F I hpos b
  refine ⟨(c, a), ?_⟩
  change c • (1 : WordIdealQuotient F I) + a.val = b
  exact hb.symm

theorem positiveWordIdealQuotient_not_finite
    (hinfinite : ¬ Module.Finite F (WordIdealQuotient F I)) :
    ¬ Module.Finite F (PositiveWordIdealQuotient F I hpos) := by
  intro hfinite
  letI : Module.Finite F (PositiveWordIdealQuotient F I hpos) := hfinite
  exact hinfinite (FiniteDimensional.of_surjective (scalarPlusPositiveLinearMap F I hpos)
    (scalarPlusPositiveLinearMap_surjective F I hpos))

theorem positiveWordIdealQuotient_ordinaryPrime
    (hB : OrdinaryTwoSidedPrime (WordIdealQuotient F I)) (htail : NoWordTail F I) :
    CriticalGK2.PrimeInheritance.OrdinaryNonUnitalPrime (PositiveWordIdealQuotient F I hpos) :=
  CriticalGK2.PrimeInheritance.ordinaryPrime_of_scalar_positive_decomposition F
    (positiveWordIdealSubalgebra F I hpos) hB (positiveWordIdeal_scalar_split F I hpos)
    (positiveWordIdealQuotient_nonzero F I hpos htail)

/-- Every actual nonzero positive element survives a proved finite target. -/
theorem positiveWordIdealQuotient_residually_finite_dimensional
    (hhom : WordIdealHomogeneous F I) (a : PositiveWordIdealQuotient F I hpos) (ha : a ≠ 0) :
    ∃ N : ℕ, 0 < N ∧
      ((CriticalGK2.GenericResidual.factor F I N).toNonUnitalAlgHom.comp
        (positiveWordIdealInclusion F I hpos)) a ≠ 0 :=
  CriticalGK2.GenericResidual.included_algebra_residually_finite_dimensional F I hhom
    (positiveWordIdealInclusion F I hpos) (positiveWordIdealInclusion_injective F I hpos) a ha

/-- One actual positive infinite ordinary-prime further quotient of the
original sparse construction, with its actual finite tail separation maps. -/
theorem sparse_exists_positive_prime_furtherQuotient (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) :
    ∃ I : TwoSidedIdeal (WordAlgebra F),
      ∃ hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0,
      allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
        (sparseDualData_primalCoherent F Λ hΛ) ≤ I ∧
      WordIdealHomogeneous F I ∧ NoWordTail F I ∧
      ¬ Module.Finite F (PositiveWordIdealQuotient F I hpos) ∧
      CriticalGK2.PrimeInheritance.OrdinaryNonUnitalPrime (PositiveWordIdealQuotient F I hpos) ∧
      (∀ a : PositiveWordIdealQuotient F I hpos, a ≠ 0 →
        ∃ N : ℕ, 0 < N ∧ ((CriticalGK2.GenericResidual.factor F I N).toNonUnitalAlgHom.comp
          (positiveWordIdealInclusion F I hpos)) a ≠ 0) := by
  obtain ⟨I, hEI, hhom, htail, hBprime, hinfinite, hfinite, hlower⟩ :=
    sparse_exists_ordinaryPrime_furtherQuotient F Λ hΛ
  let hpos := homogeneous_noWordTail_augmentation_eq_zero F I hhom htail
  exact ⟨I, hpos, hEI, hhom, htail, positiveWordIdealQuotient_not_finite F I hpos hinfinite,
    positiveWordIdealQuotient_ordinaryPrime F I hpos hBprime htail,
    positiveWordIdealQuotient_residually_finite_dimensional F I hpos hhom⟩

#print axioms CriticalGK2.Actual.positiveWordIdealFactor_surjective
#print axioms CriticalGK2.Actual.positiveWordIdealQuotient_not_finite
#print axioms CriticalGK2.Actual.positiveWordIdealQuotient_ordinaryPrime
#print axioms CriticalGK2.Actual.positiveWordIdealQuotient_residually_finite_dimensional
#print axioms CriticalGK2.Actual.sparse_exists_positive_prime_furtherQuotient

end

end CriticalGK2.Actual
