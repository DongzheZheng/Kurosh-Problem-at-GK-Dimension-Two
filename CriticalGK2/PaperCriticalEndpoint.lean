import CriticalGK2.PrimeCriticalDefault
import CriticalGK2.UnitalCriticalEndpoint

/-! Field-only endpoint combining all positive properties and their actual
unitization corollary for the same witness I and the same literal Q. -/

namespace CriticalGK2.Actual

noncomputable section

open Filter TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (F : Type*) [Field F]

theorem exists_same_prime_critical_algebra_and_absolute_unitization :
    ∃ I : TwoSidedIdeal (WordAlgebra F),
      ∃ hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0,
      ∃ hEI : allCutTwoSidedIdeal F
        (sparseDualData F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges)
        (sparseDualData_primalCoherent F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges) ≤ I,
      DefaultPrimeCriticalProperties F I hpos hEI ∧
      (Algebra.adjoin F (Set.range (positiveUnitizationGenerator F I hpos
        (sparseDualData F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges)
        (sparseDualData_primalCoherent F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges)
        hEI)) = ⊤) ∧
      (¬ Module.Finite F (Unitization F (PositiveWordIdealQuotient F I hpos))) ∧
      (Filter.limsup (CriticalGK2.Growth.logarithmicGrowthRatio
        (positiveUnitizationDegreeGrowth F I hpos)) atTop = 2) ∧
      (∀ (K : Type*) [Field K] [Algebra F K],
        ∀ r : ℕ, 0 < r → Algebra.IsAlgebraic K
          (Matrix (Fin r) (Fin r)
            ((Unitization F (PositiveWordIdealQuotient F I hpos)) ⊗[F] K))) := by
  obtain ⟨I, hpos, hEI, hQ⟩ := exists_prime_critical_gk_two_absolute_nil_default F
  have hhom : WordIdealHomogeneous F I := hQ.1
  have htail : NoWordTail F I := hQ.2.1
  have hinfiniteQ : ¬ Module.Finite F (PositiveWordIdealQuotient F I hpos) := hQ.2.2.2.2.1
  refine ⟨I, hpos, hEI, hQ,
    positiveUnitization_two_generated F I hpos
      (sparseDualData F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges)
      (sparseDualData_primalCoherent F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges) hEI,
    positiveUnitization_not_finite F I hpos hinfiniteQ,
    positiveUnitizationGrowth_logarithmic_limsup F I hpos
      (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges hEI hhom htail, ?_⟩
  intro K _ _
  exact unitization_tensor_matrix_algebraic_of_scalar_matrix_nil F K
    (PositiveWordIdealQuotient F I hpos)
    (sparse_positiveWordIdeal_scalar_matrix_nil F K I hpos
      (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges hEI)

#check CriticalGK2.Actual.exists_same_prime_critical_algebra_and_absolute_unitization
#print axioms CriticalGK2.Actual.exists_same_prime_critical_algebra_and_absolute_unitization

end

end CriticalGK2.Actual
