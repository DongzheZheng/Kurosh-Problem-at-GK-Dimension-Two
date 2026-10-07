import CriticalGK2.SparseAbsoluteMatrixNil
import CriticalGK2.ScalarExtensionUnitization

/-!
# Actual absolute matrix nilness and scalar-extended unitization

The same actual quotient constructed over F is used over every extension K.
Its right tensor presentation is matrix-nil; proved multiplicative tensor
commutation gives its canonical left K-module presentation. The matrix
nilness theorem then implies algebraicity of its K-unitization matrices.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

theorem originalField_scalar_unitization_matrix_algebraic :
    ∀ r : ℕ, 0 < r →
      Algebra.IsAlgebraic K
        (Matrix (Fin r) (Fin r) (Unitization K (K ⊗[F] (OriginalFieldNilAlgebra F)))) :=
  scalarExtension_unitization_matrix_algebraic F K (OriginalFieldNilAlgebra F)
    (originalField_absolute_matrix_nil F K)

/-- The same actual object has infinite dimension, absolutely nil matrices,
and algebraic unitized matrices over the arbitrary extension field. -/
theorem originalField_absolute_unitization_endpoint :
    (¬ Module.Finite F (OriginalFieldNilAlgebra F)) ∧
    (∀ r : ℕ, 0 < r →
      ∀ M : Matrix (Fin r) (Fin r) ((OriginalFieldNilAlgebra F) ⊗[F] K),
        ∃ e : ℕ, positivePower M e = 0) ∧
    (∀ r : ℕ, 0 < r →
      Algebra.IsAlgebraic K
        (Matrix (Fin r) (Fin r) (Unitization K (K ⊗[F] (OriginalFieldNilAlgebra F))))) :=
  ⟨(originalField_endpoint F).1, originalField_absolute_matrix_nil F K,
    originalField_scalar_unitization_matrix_algebraic F K⟩

#print axioms CriticalGK2.Actual.originalField_scalar_unitization_matrix_algebraic
#print axioms CriticalGK2.Actual.originalField_absolute_unitization_endpoint

end

end CriticalGK2.Actual
