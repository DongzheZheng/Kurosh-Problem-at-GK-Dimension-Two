import CriticalGK2.DualWordBridge
import CriticalGK2.ActualSuffixContraction

/-!
# A complete actual zero block kills whole-word matrix evaluation

These are kernel inclusions for the actual homogeneous dual evaluator. The
multiplicative identification is consumed from the proved word-coefficient
bridge. Actual prefix and suffix contraction spaces consequently retain zero
evaluation under every whole-exterior functional.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F : Type*) [Field F]

/-- Every actual retained word with a complete zero first block evaluates to zero. -/
theorem actualLeftBlockSpace_le_matrix_kernel (C : Type*) [CommRing C] [Algebra F C]
    (k a b : ℕ) (v : Bool → Matrix (Fin k) (Fin k) C)
    (W : Submodule F (HomogeneousDual F a))
    (hW : W ≤ LinearMap.ker (actualDualMatrixEvaluation F C k a v)) :
    actualLeftBlockSpace F a b W ≤ LinearMap.ker (actualDualMatrixEvaluation F C k (a + b) v) := by
  rintro z ⟨w, ⟨u, rfl⟩, rfl⟩
  change actualDualMatrixEvaluation F C k (a + b) v
    (homogeneousDualTensorConcat F a b
      (W.subtype.rTensor (HomogeneousDual F b) u)) = 0
  induction u using TensorProduct.induction_on with
  | zero =>
      rw [(W.subtype.rTensor (HomogeneousDual F b)).map_zero,
        (homogeneousDualTensorConcat F a b).map_zero,
        (actualDualMatrixEvaluation F C k (a + b) v).map_zero]
  | add u u' hu hu' => simp only [map_add, hu, hu', add_zero]
  | tmul φ ψ =>
      simp only [LinearMap.rTensor_tmul]
      rw [actualDualMatrixEvaluation_tensorConcat]
      change actualDualMatrixEvaluation F C k a v φ.val *
        actualDualMatrixEvaluation F C k b v ψ = 0
      rw [hW φ.property, zero_mul]

/-- Every actual retained word with a complete zero last block evaluates to zero. -/
theorem actualRightBlockSpace_le_matrix_kernel (C : Type*) [CommRing C] [Algebra F C]
    (k b c : ℕ) (v : Bool → Matrix (Fin k) (Fin k) C)
    (W : Submodule F (HomogeneousDual F c))
    (hW : W ≤ LinearMap.ker (actualDualMatrixEvaluation F C k c v)) :
    actualRightBlockSpace F b c W ≤ LinearMap.ker (actualDualMatrixEvaluation F C k (b + c) v) := by
  rintro z ⟨w, ⟨u, rfl⟩, rfl⟩
  change actualDualMatrixEvaluation F C k (b + c) v
    (homogeneousDualTensorConcat F b c
      (W.subtype.lTensor (HomogeneousDual F b) u)) = 0
  induction u using TensorProduct.induction_on with
  | zero =>
      rw [(W.subtype.lTensor (HomogeneousDual F b)).map_zero,
        (homogeneousDualTensorConcat F b c).map_zero,
        (actualDualMatrixEvaluation F C k (b + c) v).map_zero]
  | add u u' hu hu' => simp only [map_add, hu, hu', add_zero]
  | tmul φ ψ =>
      simp only [LinearMap.lTensor_tmul]
      rw [actualDualMatrixEvaluation_tensorConcat]
      change actualDualMatrixEvaluation F C k b v φ *
        actualDualMatrixEvaluation F C k c v ψ.val = 0
      rw [hW ψ.property, mul_zero]

/-- An arbitrary functional on the whole external dual space preserves zero
matrix evaluation of an actual complete first block. -/
theorem actualPrefixContraction_matrix_evaluation_eq_zero (C : Type*) [CommRing C] [Algebra F C]
    (k a b c : ℕ) (v : Bool → Matrix (Fin k) (Fin k) C)
    (W : Submodule F (HomogeneousDual F a))
    (hW : W ≤ LinearMap.ker (actualDualMatrixEvaluation F C k a v))
    (η : Module.Dual F (HomogeneousDual F c))
    (z : HomogeneousDual F (a + (b + c)))
    (hz : z ∈ actualLeftBlockTripleSpace F a b c W) :
    actualDualMatrixEvaluation F C k (a + b) v (actualPrefixContraction F a b c η z) = 0 :=
  actualLeftBlockSpace_le_matrix_kernel F C k a b v W hW
    (actualPrefixContraction_mem F a b c W η z hz)

/-- The mirror actual suffix contraction result. -/
theorem actualSuffixContractionLeftAssociated_matrix_evaluation_eq_zero (C : Type*) [CommRing C] [Algebra F C]
    (k a b c : ℕ) (v : Bool → Matrix (Fin k) (Fin k) C)
    (W : Submodule F (HomogeneousDual F c))
    (hW : W ≤ LinearMap.ker (actualDualMatrixEvaluation F C k c v))
    (η : Module.Dual F (HomogeneousDual F a))
    (z : HomogeneousDual F ((a + b) + c))
    (hz : z ∈ actualRightBlockTripleSpaceLeftAssociated F a b c W) :
    actualDualMatrixEvaluation F C k (b + c) v (actualSuffixContractionLeftAssociated F a b c η z) = 0 :=
  actualRightBlockSpace_le_matrix_kernel F C k b c v W hW
    (actualSuffixContractionLeftAssociated_mem F a b c W η z hz)

end

end CriticalGK2.Actual
