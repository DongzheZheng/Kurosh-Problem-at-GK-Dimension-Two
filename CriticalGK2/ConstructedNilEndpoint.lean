import CriticalGK2.PositiveGeneration
import CriticalGK2.AbsoluteUnitizationEndpoint

/-!
# The same two-generated infinite algebra over every scalar extension

This endpoint combines actual generation, actual infinite dimensionality,
actual scalar-extension matrix nilness and actual scalar-extension unitization.
The algebra is fixed over F before the arbitrary extension K is introduced.
The construction and readback theorems supply each property of this algebra.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F : Type*) [Field F]

/-- A single actual two-generated infinite positive quotient over F,
absolutely matrix nil and with algebraic matrix unitizations after every
field extension. -/
theorem originalField_constructed_absolute_nil_endpoint :
    (¬ Module.Finite F (OriginalFieldNilAlgebra F)) ∧
    (NonUnitalAlgebra.adjoin F (Set.range (originalFieldGenerator F)) = ⊤) ∧
    (∀ (K : Type*) [Field K] [Algebra F K],
      (∀ r : ℕ, 0 < r →
        ∀ M : Matrix (Fin r) (Fin r) ((OriginalFieldNilAlgebra F) ⊗[F] K),
          ∃ e : ℕ, positivePower M e = 0) ∧
      (∀ r : ℕ, 0 < r → Algebra.IsAlgebraic K
        (Matrix (Fin r) (Fin r) (Unitization K (K ⊗[F] (OriginalFieldNilAlgebra F)))))) := by
  refine ⟨(originalField_endpoint F).1, originalField_two_generated F, ?_⟩
  intro K _ _
  exact ⟨originalField_absolute_matrix_nil F K,
    originalField_scalar_unitization_matrix_algebraic F K⟩

#print axioms CriticalGK2.Actual.originalField_constructed_absolute_nil_endpoint

end

end CriticalGK2.Actual
