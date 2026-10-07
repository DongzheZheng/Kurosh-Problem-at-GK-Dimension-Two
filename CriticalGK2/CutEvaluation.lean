import CriticalGK2.HomogeneousCutTensor
import CriticalGK2.DualDegreeBridge

/-!
# Actual long-cut kernels imply actual all-cut evaluation vanishing

The endpoint scalar factors are retained. A cut whose first side is long uses
its actual L annihilator kernel; otherwise the second side is long and uses
its actual R annihilator kernel. The construction must supply these two long
completion kernels. This module proves the all-cut linear-algebra step.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F C : Type*) [Field F] [CommRing C] [Algebra F C]
variable (k : ℕ) (v : Bool → Matrix (Fin k) (Fin k) C)

@[simp] theorem actualDualMatrixEvaluation_degreeCast {a b : ℕ}
    (hab : a = b) (φ : HomogeneousDual F a) :
    actualDualMatrixEvaluation F C k b v (homogeneousDualDegreeCast F hab φ) =
      actualDualMatrixEvaluation F C k a v φ := by
  simp only [actualDualMatrixEvaluation, LinearMap.comp_apply, dualToAmbient_degreeCast]

theorem actualDualTensorProduct_le_eval_kernel_left (a b : ℕ)
    (S : Submodule F (HomogeneousDual F a)) (T : Submodule F (HomogeneousDual F b))
    (hS : S ≤ LinearMap.ker (actualDualMatrixEvaluation F C k a v)) :
    actualDualTensorProduct F a b S T ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k (a + b) v) := by
  rintro φ ⟨z, ⟨w, rfl⟩, rfl⟩
  change actualDualMatrixEvaluation F C k (a + b) v
    (homogeneousDualTensorConcat F a b (TensorProduct.map S.subtype T.subtype w)) = 0
  induction w using TensorProduct.induction_on with
  | zero =>
    rw [(TensorProduct.map S.subtype T.subtype).map_zero,
      (homogeneousDualTensorConcat F a b).map_zero,
      (actualDualMatrixEvaluation F C k (a + b) v).map_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul x y =>
    simp only [TensorProduct.map_tmul]
    rw [actualDualMatrixEvaluation_tensorConcat]
    change actualDualMatrixEvaluation F C k a v x.val *
      actualDualMatrixEvaluation F C k b v y.val = 0
    rw [hS x.property, zero_mul]

theorem actualDualTensorProduct_le_eval_kernel_right (a b : ℕ)
    (S : Submodule F (HomogeneousDual F a)) (T : Submodule F (HomogeneousDual F b))
    (hT : T ≤ LinearMap.ker (actualDualMatrixEvaluation F C k b v)) :
    actualDualTensorProduct F a b S T ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k (a + b) v) := by
  rintro φ ⟨z, ⟨w, rfl⟩, rfl⟩
  change actualDualMatrixEvaluation F C k (a + b) v
    (homogeneousDualTensorConcat F a b (TensorProduct.map S.subtype T.subtype w)) = 0
  induction w using TensorProduct.induction_on with
  | zero =>
    rw [(TensorProduct.map S.subtype T.subtype).map_zero,
      (homogeneousDualTensorConcat F a b).map_zero,
      (actualDualMatrixEvaluation F C k (a + b) v).map_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul x y =>
    simp only [TensorProduct.map_tmul]
    rw [actualDualMatrixEvaluation_tensorConcat]
    change actualDualMatrixEvaluation F C k a v x.val *
      actualDualMatrixEvaluation F C k b v y.val = 0
    rw [hT y.property, mul_zero]

/-- The precise all-cut evaluation step, with the remaining two long
completion-kernel obligations displayed as mathematical inputs. -/
theorem allCut_evaluation_zero_of_long_completions
    (W : DyadicDualData F) (ν n : ℕ) (hn : 2 * ν ≤ n)
    (hleft : ∀ m, ν ≤ m →
      (homogeneousLeftCompletion F W m).dualAnnihilator ≤
        LinearMap.ker (actualDualMatrixEvaluation F C k m v))
    (hright : ∀ m, ν ≤ m →
      (homogeneousRightCompletion F W m).dualAnnihilator ≤
        LinearMap.ker (actualDualMatrixEvaluation F C k m v)) :
    (homogeneousAllCutComponent F W n).dualAnnihilator ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k n v) := by
  rw [homogeneousAllCutComponent_dualAnnihilator_eq_actualTensorCuts]
  apply iSup_le
  intro i
  have hkernel : actualDualTensorProduct F i.val (n - i.val)
      (homogeneousLeftCompletion F W i.val).dualAnnihilator
      (homogeneousRightCompletion F W (n - i.val)).dualAnnihilator ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k (i.val + (n - i.val)) v) := by
    by_cases hlong : ν ≤ i.val
    · exact actualDualTensorProduct_le_eval_kernel_left F C k v _ _ _ _ (hleft _ hlong)
    · have hlong' : ν ≤ n - i.val := by omega
      exact actualDualTensorProduct_le_eval_kernel_right F C k v _ _ _ _ (hright _ hlong')
  rintro φ ⟨ψ, hψ, rfl⟩
  change actualDualMatrixEvaluation F C k n v
    (homogeneousDualDegreeCast F (homogeneousCutDegree n i) ψ) = 0
  rw [actualDualMatrixEvaluation_degreeCast]
  exact hkernel hψ

end

end CriticalGK2.Actual
