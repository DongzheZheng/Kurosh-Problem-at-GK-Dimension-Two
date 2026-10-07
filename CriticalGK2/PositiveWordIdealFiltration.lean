import CriticalGK2.PositiveWordIdealGrowth
import CriticalGK2.PositiveWordIdealGeneration
import CriticalGK2.PositiveWordFiltration

/-! The actual further positive quotient has the literal word filtration in
its two actual generators. Its cutoff spaces are the actual images of the
original cutoff spaces under the true non-unital quotient homomorphism. -/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]
variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)
variable (W : DyadicDualData F) (hW : PrimalCoherent F W)
variable (hEI : allCutTwoSidedIdeal F W hW ≤ I)

def positiveWordIdealFactorLinearMap :
    PositiveAllCutQuotient F W hW →ₗ[F] PositiveWordIdealQuotient F I hpos where
  toFun := positiveWordIdealFactor F I hpos W hW hEI
  map_add' := (positiveWordIdealFactor F I hpos W hW hEI).map_add
  map_smul' := (positiveWordIdealFactor F I hpos W hW hEI).map_smul

theorem positiveIdealDegreeFiltration_map_inclusion (N : ℕ) :
    (positiveIdealDegreeFiltration F I hpos N).map
      (positiveWordIdealLinearInclusion F I hpos) = idealPositiveDegreeFiltration F I N := by
  change ((idealPositiveDegreeFiltration F I N).comap
      (positiveWordIdealSubalgebra F I hpos).toSubmodule.subtype).map
      (positiveWordIdealSubalgebra F I hpos).toSubmodule.subtype = _
  rw [Submodule.map_comap_subtype]
  exact inf_eq_right.mpr (idealPositiveDegreeFiltration_le_positive F I hpos N)

theorem positiveIdealFiltration_eq_map (N : ℕ) :
    positiveIdealDegreeFiltration F I hpos N =
      (positiveDegreeFiltration F W hW N).map
        (positiveWordIdealFactorLinearMap F I hpos W hW hEI) := by
  apply Submodule.map_injective_of_injective
    (f := positiveWordIdealLinearInclusion F I hpos)
    (positiveWordIdealLinearInclusion_injective F I hpos)
  rw [positiveIdealDegreeFiltration_map_inclusion]
  rw [← Submodule.map_comp]
  change idealPositiveDegreeFiltration F I N =
    (positiveDegreeFiltration F W hW N).map (furtherPositiveLinearMap F W hW I hEI)
  exact idealPositiveFiltration_eq_map F W hW I hEI N

def boundedPositiveIdealWordImage (N : ℕ) (w : BoundedPositiveWord N) :
    PositiveWordIdealQuotient F I hpos :=
  positiveWordIdealFactor F I hpos W hW hEI (boundedPositiveWordImage F W hW N w)

def positiveIdealWordFiltration (N : ℕ) :
    Submodule F (PositiveWordIdealQuotient F I hpos) :=
  Submodule.span F (Set.range (boundedPositiveIdealWordImage F I hpos W hW hEI N))

theorem positiveIdealDegreeFiltration_eq_wordFiltration (N : ℕ) :
    positiveIdealDegreeFiltration F I hpos N =
      positiveIdealWordFiltration F I hpos W hW hEI N := by
  rw [positiveIdealFiltration_eq_map F I hpos W hW hEI N,
    positiveDegreeFiltration_eq_wordFiltration]
  unfold positiveWordFiltration positiveIdealWordFiltration
  rw [Submodule.map_span]
  congr 1
  ext a
  constructor
  · rintro ⟨x, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨boundedPositiveWordImage F W hW N w, ⟨w, rfl⟩, rfl⟩

theorem positiveIdealDegreeGrowth_eq_wordSpan_finrank (N : ℕ) :
    positiveIdealDegreeGrowth F I hpos N = Module.finrank F
      (positiveIdealWordFiltration F I hpos W hW hEI N) := by
  unfold positiveIdealDegreeGrowth
  rw [positiveIdealDegreeFiltration_eq_wordFiltration F I hpos W hW hEI N]

#print axioms CriticalGK2.Actual.positiveIdealFiltration_eq_map
#print axioms CriticalGK2.Actual.positiveIdealDegreeFiltration_eq_wordFiltration
#print axioms CriticalGK2.Actual.positiveIdealDegreeGrowth_eq_wordSpan_finrank

end

end CriticalGK2.Actual
