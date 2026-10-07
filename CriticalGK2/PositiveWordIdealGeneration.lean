import CriticalGK2.PositiveWordIdealTransfer
import CriticalGK2.PositiveGeneration

/-! The two literal original generators generate the actual further positive
quotient. The proof pulls its actual adjoin back along the actual surjection. -/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]
variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)
variable (W : DyadicDualData F) (hW : PrimalCoherent F W)
variable (hEI : allCutTwoSidedIdeal F W hW ≤ I)

def positiveIdealGenerator (b : Bool) : PositiveWordIdealQuotient F I hpos :=
  positiveWordIdealFactor F I hpos W hW hEI (positiveGenerator F W hW b)

theorem positiveWordIdealQuotient_two_generated :
    NonUnitalAlgebra.adjoin F (Set.range (positiveIdealGenerator F I hpos W hW hEI)) = ⊤ := by
  let S := NonUnitalAlgebra.adjoin F
    (Set.range (positiveIdealGenerator F I hpos W hW hEI))
  let f := positiveWordIdealFactor F I hpos W hW hEI
  have hsource : S.comap f = ⊤ := by
    apply positiveSubalgebra_eq_top_of_generators_mem F W hW
    intro b
    change f (positiveGenerator F W hW b) ∈ S
    exact NonUnitalAlgebra.subset_adjoin F ⟨b, rfl⟩
  apply eq_top_iff.mpr
  intro a _
  obtain ⟨x, rfl⟩ := positiveWordIdealFactor_surjective F I hpos W hW hEI a
  have hx : x ∈ S.comap f := by
    rw [hsource]
    trivial
  exact hx

#print axioms CriticalGK2.Actual.positiveWordIdealQuotient_two_generated

end

end CriticalGK2.Actual
