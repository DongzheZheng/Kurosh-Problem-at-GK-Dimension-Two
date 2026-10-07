import CriticalGK2.SparseMatrixNil
import CriticalGK2.ScalarExtensionMatrixDescent

/-!
# All field extensions of the same actual positive quotient

The algebra is constructed over F. Its positive quotient tensored with an
arbitrary extension K is matrix-nil. The proof specializes the universal
all-cut evaluator theorem to Polynomial K and applies scalar-extension
readback and descent.
-/

namespace CriticalGK2.Actual

noncomputable section

open CriticalGK2.Automaton
open TensorProduct

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- The same concrete sparse quotient has nil matrices over every extension
field, with ordinary tensor-product multiplication. -/
theorem sparse_scalar_matrix_nil (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) :
    ∀ r : ℕ, 0 < r →
      ∀ M : Matrix (Fin r) (Fin r)
        ((PositiveAllCutQuotient F (sparseDualData F Λ hΛ)
          (sparseDualData_primalCoherent F Λ hΛ)) ⊗[F] K),
        ∃ e : ℕ, positivePower M e = 0 := by
  apply positive_scalar_matrix_nil_of_allCut_evaluation_zero F K
    (sparseDualData F Λ hΛ) (sparseDualData_primalCoherent F Λ hΛ)
  intro r hr d hd
  obtain ⟨N, hN⟩ := sparse_allCut_evaluation_zero F Λ hΛ r d hr hd
  exact ⟨N, fun c n hn => hN (Polynomial K) (finiteLetterTransition c) n hn⟩

/-- The completely specified original-field object, with its arbitrary
scalar extension, has nil matrices at every positive matrix order. -/
theorem originalField_absolute_matrix_nil :
    ∀ r : ℕ, 0 < r →
      ∀ M : Matrix (Fin r) (Fin r) ((OriginalFieldNilAlgebra F) ⊗[F] K),
        ∃ e : ℕ, positivePower M e = 0 :=
  sparse_scalar_matrix_nil F K (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges

/-- Infinite dimension and absolute stable nilness for the same quotient. -/
theorem originalField_infinite_absolute_nil :
    (¬ Module.Finite F (OriginalFieldNilAlgebra F)) ∧
    (∀ r : ℕ, 0 < r →
      ∀ M : Matrix (Fin r) (Fin r) ((OriginalFieldNilAlgebra F) ⊗[F] K),
        ∃ e : ℕ, positivePower M e = 0) :=
  ⟨(originalField_endpoint F).1, originalField_absolute_matrix_nil F K⟩

#print axioms CriticalGK2.Actual.sparse_scalar_matrix_nil
#print axioms CriticalGK2.Actual.originalField_absolute_matrix_nil
#print axioms CriticalGK2.Actual.originalField_infinite_absolute_nil

end

end CriticalGK2.Actual
