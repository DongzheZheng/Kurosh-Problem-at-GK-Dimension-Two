import CriticalGK2.ActualWordSpaces
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Actual scalar extension of the noncommutative free word algebra

The word monoid is noncommutative.  The coefficient-tensor equivalence is
constructed from the actual word basis, and its multiplicativity is proved
on singleton words.
-/

namespace CriticalGK2.Actual

open TensorProduct

noncomputable section

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

local instance : DecidableEq Word := Classical.decEq _

/-- The actual coefficient equivalence for scalar extension of the actual
noncommutative free word algebra. -/
def wordCoefficientTensorEquiv :
    WordAlgebra F ⊗[F] K ≃ₗ[F] WordAlgebra K :=
  TensorProduct.equivFinsuppOfBasisLeft (N := K)
    (Finsupp.basisSingleOne : Module.Basis Word F (WordAlgebra F))

/-- Actual coefficient-by-coefficient reconstruction in the original tensor space. -/
def coefficientTensorMap : WordAlgebra K →ₗ[F] WordAlgebra F ⊗[F] K :=
  (wordCoefficientTensorEquiv F K).symm.toLinearMap

@[simp]
theorem coefficientTensorMap_single (w : Word) (c : K) :
    coefficientTensorMap F K (MonoidAlgebra.single w c) =
      MonoidAlgebra.single w (1 : F) ⊗ₜ[F] c := by
  classical
  apply (wordCoefficientTensorEquiv F K).injective
  change wordCoefficientTensorEquiv F K
      ((wordCoefficientTensorEquiv F K).symm (MonoidAlgebra.single w c)) =
    wordCoefficientTensorEquiv F K (MonoidAlgebra.single w (1 : F) ⊗ₜ[F] c)
  rw [LinearEquiv.apply_symm_apply]
  apply Finsupp.ext
  intro v
  change (Finsupp.single w c) v =
    TensorProduct.equivFinsuppOfBasisLeft
      (Finsupp.basisSingleOne : Module.Basis Word F (WordAlgebra F))
      (MonoidAlgebra.single w (1 : F) ⊗ₜ[F] c) v
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  change (Finsupp.single w c) v = (Finsupp.single w (1 : F)) v • c
  by_cases h : w = v
  · subst v
    simp
  · simp [Finsupp.single_apply, h]

/-- The exact actual coefficient formula on an actual pure tensor. -/
theorem wordCoefficientTensorEquiv_tmul_coefficient
    (P : WordAlgebra F) (c : K) (w : Word) :
    wordCoefficientTensorEquiv F K (P ⊗ₜ[F] c) w =
      algebraMap F K (P w) * c := by
  change TensorProduct.equivFinsuppOfBasisLeft
    (Finsupp.basisSingleOne : Module.Basis Word F (WordAlgebra F)) (P ⊗ₜ[F] c) w = _
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  change P w • c = _
  exact Algebra.smul_def (P w) c

@[simp]
theorem wordCoefficientTensorEquiv_single_tmul (w : Word) (c : K) :
    wordCoefficientTensorEquiv F K (MonoidAlgebra.single w (1 : F) ⊗ₜ[F] c) =
      MonoidAlgebra.single w c := by
  apply (wordCoefficientTensorEquiv F K).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (coefficientTensorMap_single F K w c).symm

/-- Multiplicativity of the actual coefficient-tensor map, proved directly
on actual finite word supports. -/
theorem coefficientTensorMap_mul (P Q : WordAlgebra K) :
    coefficientTensorMap F K (P * Q) =
      coefficientTensorMap F K P * coefficientTensorMap F K Q := by
  classical
  have hmul : ∀ p q : Word →₀ K,
      coefficientTensorMap F K (MonoidAlgebra.ofCoeff p * MonoidAlgebra.ofCoeff q) =
        coefficientTensorMap F K (MonoidAlgebra.ofCoeff p) *
          coefficientTensorMap F K (MonoidAlgebra.ofCoeff q) := by
    intro p q
    induction p using Finsupp.induction with
    | zero =>
        change coefficientTensorMap F K ((0 : WordAlgebra K) * MonoidAlgebra.ofCoeff q) =
          coefficientTensorMap F K (0 : WordAlgebra K) *
            coefficientTensorMap F K (MonoidAlgebra.ofCoeff q)
        simp only [zero_mul, LinearMap.map_zero]
    | single_add w c p hw hc ih =>
        change coefficientTensorMap F K
            ((MonoidAlgebra.single w c + MonoidAlgebra.ofCoeff p) * MonoidAlgebra.ofCoeff q) =
          coefficientTensorMap F K (MonoidAlgebra.single w c + MonoidAlgebra.ofCoeff p) *
            coefficientTensorMap F K (MonoidAlgebra.ofCoeff q)
        rw [add_mul, map_add, map_add, add_mul, ih]
        congr 1
        clear ih
        induction q using Finsupp.induction with
        | zero =>
            change coefficientTensorMap F K (MonoidAlgebra.single w c * (0 : WordAlgebra K)) =
              coefficientTensorMap F K (MonoidAlgebra.single w c) *
                coefficientTensorMap F K (0 : WordAlgebra K)
            simp only [mul_zero, LinearMap.map_zero]
        | single_add v a q hv ha ihq =>
            change coefficientTensorMap F K
                (MonoidAlgebra.single w c * (MonoidAlgebra.single v a + MonoidAlgebra.ofCoeff q)) =
              coefficientTensorMap F K (MonoidAlgebra.single w c) *
                coefficientTensorMap F K (MonoidAlgebra.single v a + MonoidAlgebra.ofCoeff q)
            rw [mul_add, map_add, map_add, mul_add, ihq]
            simp [MonoidAlgebra.single_mul_single, Algebra.TensorProduct.tmul_mul_tmul]
  exact hmul (MonoidAlgebra.coeff P) (MonoidAlgebra.coeff Q)

/-- The actual noncommutative coefficient-tensor equivalence is a ring
isomorphism; its underlying map is the explicit coefficient tensor map. -/
def coefficientTensorRingEquiv : WordAlgebra K ≃+* WordAlgebra F ⊗[F] K where
  __ := (wordCoefficientTensorEquiv F K).symm.toAddEquiv
  map_mul' := coefficientTensorMap_mul F K

@[simp]
theorem coefficientTensorRingEquiv_apply (P : WordAlgebra K) :
    coefficientTensorRingEquiv F K P = coefficientTensorMap F K P := rfl

@[simp]
theorem coefficientTensorRingEquiv_symm_apply (z : WordAlgebra F ⊗[F] K) :
    (coefficientTensorRingEquiv F K).symm z = wordCoefficientTensorEquiv F K z := rfl

#print axioms CriticalGK2.Actual.coefficientTensorMap_mul
#print axioms CriticalGK2.Actual.coefficientTensorRingEquiv

end

end CriticalGK2.Actual
