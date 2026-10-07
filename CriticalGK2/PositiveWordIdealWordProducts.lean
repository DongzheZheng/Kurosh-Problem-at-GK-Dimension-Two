import CriticalGK2.PositiveWordIdealFiltration

/-! Literal word products and homogeneous degree-one generators in the
actual further positive quotient. The n-th positive space is degree n+1. -/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]
variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)
variable (W : DyadicDualData F) (hW : PrimalCoherent F W)
variable (hEI : allCutTwoSidedIdeal F W hW ≤ I)

def positiveIdealWordImage (w : Word) (hw : w ≠ 1) :
    PositiveWordIdealQuotient F I hpos :=
  positiveWordIdealFactor F I hpos W hW hEI (positiveWordImage F W hW w hw)

theorem positiveIdealWordImage_mul (u v : Word) (hu : u ≠ 1) (hv : v ≠ 1) :
    positiveIdealWordImage F I hpos W hW hEI (u * v) (word_mul_ne_one_of_left u v hu) =
      positiveIdealWordImage F I hpos W hW hEI u hu *
        positiveIdealWordImage F I hpos W hW hEI v hv := by
  unfold positiveIdealWordImage
  rw [positiveWordImage_mul, map_mul]

theorem positiveIdealWordImage_letter (b : Bool) (hb : (FreeMonoid.of b : Word) ≠ 1) :
    positiveIdealWordImage F I hpos W hW hEI (FreeMonoid.of b) hb =
      positiveIdealGenerator F I hpos W hW hEI b := by
  unfold positiveIdealWordImage positiveIdealGenerator
  rw [positiveWordImage_letter]

theorem positiveIdealGenerator_mem_degree_one (b : Bool) :
    positiveIdealGenerator F I hpos W hW hEI b ∈ positiveIdealDegreeSpace F I hpos 0 := by
  change wordIdealQuotientMap F I (MonoidAlgebra.single (FreeMonoid.of b) 1) ∈
    idealDegreeSpace F I (0 + 1)
  exact ⟨MonoidAlgebra.single (FreeMonoid.of b) 1,
    monomial_mem_homogeneous F 1 ⟨FreeMonoid.of b, FreeMonoid.length_of b⟩ 1, rfl⟩

#print axioms CriticalGK2.Actual.positiveIdealWordImage_mul
#print axioms CriticalGK2.Actual.positiveIdealWordImage_letter
#print axioms CriticalGK2.Actual.positiveIdealGenerator_mem_degree_one

end

end CriticalGK2.Actual
