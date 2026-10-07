import CriticalGK2.ActualUnitizationGrowthEndpoint
import CriticalGK2.UnitizationScalarBaseChange

/-! Field-only unital existence corollary. All scalar extensions are the
literal tensor product of the same unitization fixed before K is chosen,
with its standard right K-algebra structure. -/

namespace CriticalGK2.Actual

noncomputable section

open Filter
open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (F : Type*) [Field F]

theorem exists_unital_critical_gk_two_absolute_algebraic :
    ∃ I : TwoSidedIdeal (WordAlgebra F),
      ∃ hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0,
      ∃ hEI : allCutTwoSidedIdeal F
        (sparseDualData F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges)
        (sparseDualData_primalCoherent F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges) ≤ I,
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
  obtain ⟨I, hEI, hhom, htail, hprime, hinfinite, hfinite, hlower⟩ :=
    sparse_exists_ordinaryPrime_furtherQuotient F
      (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges
  let hpos := homogeneous_noWordTail_augmentation_eq_zero F I hhom htail
  have hinfiniteQ := positiveWordIdealQuotient_not_finite F I hpos hinfinite
  refine ⟨I, hpos, hEI,
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

#check CriticalGK2.Actual.exists_unital_critical_gk_two_absolute_algebraic
#print axioms CriticalGK2.Actual.exists_unital_critical_gk_two_absolute_algebraic

end

end CriticalGK2.Actual
