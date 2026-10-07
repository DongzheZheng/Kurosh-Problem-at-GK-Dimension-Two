import CriticalGK2.LongCompletionEvaluation
import CriticalGK2.CutEvaluation

/-!
# Opaque-family event-to-all-cut interface

Exact coefficient reconstruction also transports an actual dual event kernel
back to the actual polynomial space. The long completion and all-cut steps
are combined for an ordinary opaque family, before its concrete recursive
implementation is substituted.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F C : Type*) [Field F] [CommRing C] [Algebra F C]
variable (k : ℕ) (v : Bool → Matrix (Fin k) (Fin k) C)

theorem primal_kernel_of_coefficient_dual_kernel (n : ℕ)
    (S : Submodule F (WordAlgebra F)) (hS : S ≤ homogeneous F n)
    (hdual : dualCoefficientSpace F n S ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k n v)) :
    S ≤ LinearMap.ker
      (binaryEvaluation F (Matrix (Fin k) (Fin k) C) v).toLinearMap := by
  intro P hP
  have hzero := hdual (show ambientToDual F n P ∈ dualCoefficientSpace F n S
    from ⟨P, hP, rfl⟩)
  change binaryEvaluation F (Matrix (Fin k) (Fin k) C) v
    (dualToAmbient F n (ambientToDual F n P)) = 0 at hzero
  rw [dualToAmbient_ambientToDual F n P (hS hP)] at hzero
  exact hzero

theorem actualDualFamily_allCut_evaluation_zero_of_event
    (S : ℕ → Submodule F (WordAlgebra F))
    (hS : ∀ h, S h ≤ homogeneous F (2 ^ h))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h)) (H n : ℕ)
    (hdual : actualDualFamily F S H ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k (2 ^ H) v))
    (hn : 2 * 2 ^ H ≤ n) :
    (homogeneousAllCutComponent F (actualDualFamily F S) n).dualAnnihilator ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k n v) := by
  have hker := primal_kernel_of_coefficient_dual_kernel F C k v (2 ^ H) (S H) (hS H) hdual
  apply allCut_evaluation_zero_of_long_completions F C k v (actualDualFamily F S)
    (2 ^ H) n hn
  · intro m hm
    exact actualDualFamily_leftCompletion_dualAnnihilator_le_matrix_kernel_of_ge
      F C k v S hS hproduct H m hker hm
  · intro m hm
    exact actualDualFamily_rightCompletion_dualAnnihilator_le_matrix_kernel_of_ge
      F C k v S hS hproduct H m hker hm

#print axioms CriticalGK2.Actual.actualDualFamily_allCut_evaluation_zero_of_event

end

end CriticalGK2.Actual
