import CriticalGK2.RootContractionTensorBridge
import CriticalGK2.ActualSuffixContraction

/-!
# Completion contractions retain the same actual complete blocks

The completion contractions are identified with the actual three-factor
contractions used to retain a complete zero-evaluated first or last block.
Literal degree equalities only align the original actual word spaces.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F : Type*) [Field F]

/-- Actual root prefix contraction equals the actual aligned three-factor
prefix contraction, retaining a complete first block of length a. -/
theorem actualRootPrefixContraction_eq_actualPrefixContraction (a b : ℕ)
    (η : Module.Dual F (HomogeneousDual F (2 ^ strictDyadicRoot (a + b) - (a + b))))
    (hdegree : a + (b + (2 ^ strictDyadicRoot (a + b) - (a + b))) =
      2 ^ strictDyadicRoot (a + b))
    (z : HomogeneousDual F (a + (b + (2 ^ strictDyadicRoot (a + b) - (a + b))))) :
    actualRootPrefixContraction F (a + b) η (homogeneousDualDegreeCast F hdegree z) =
      actualPrefixContraction F a b (2 ^ strictDyadicRoot (a + b) - (a + b)) η z := by
  obtain ⟨w, rfl⟩ := (homogeneousDualTripleConcat F a b
    (2 ^ strictDyadicRoot (a + b) - (a + b))).surjective z
  simp only [actualPrefixContraction, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  induction w using TensorProduct.induction_on with
  | zero =>
      rw [(homogeneousDualTripleConcat F a b
          (2 ^ strictDyadicRoot (a + b) - (a + b))).map_zero,
        (homogeneousDualDegreeCast F hdegree).map_zero,
        (actualRootPrefixContraction F (a + b) η).map_zero,
        (CriticalGK2.contractLast η).map_zero,
        (homogeneousDualTensorConcat F a b).map_zero]
  | add u v hu hv =>
      rw [(homogeneousDualTripleConcat F a b
          (2 ^ strictDyadicRoot (a + b) - (a + b))).map_add,
        (homogeneousDualDegreeCast F hdegree).map_add,
        (actualRootPrefixContraction F (a + b) η).map_add,
        (CriticalGK2.contractLast η).map_add,
        (homogeneousDualTensorConcat F a b).map_add, hu, hv]
  | tmul φ yz =>
      induction yz using TensorProduct.induction_on with
      | zero =>
          rw [TensorProduct.tmul_zero]
          rw [(homogeneousDualTripleConcat F a b
              (2 ^ strictDyadicRoot (a + b) - (a + b))).map_zero,
            (homogeneousDualDegreeCast F hdegree).map_zero,
            (actualRootPrefixContraction F (a + b) η).map_zero,
            (CriticalGK2.contractLast η).map_zero,
            (homogeneousDualTensorConcat F a b).map_zero]
      | add u v hu hv =>
          simp only [tmul_add]
          rw [(homogeneousDualTripleConcat F a b
              (2 ^ strictDyadicRoot (a + b) - (a + b))).map_add,
            (homogeneousDualDegreeCast F hdegree).map_add,
            (actualRootPrefixContraction F (a + b) η).map_add,
            (CriticalGK2.contractLast η).map_add,
            (homogeneousDualTensorConcat F a b).map_add, hu, hv]
      | tmul ψ θ =>
          have heq : homogeneousDualDegreeCast F hdegree
              (homogeneousDualTripleConcat F a b
                (2 ^ strictDyadicRoot (a + b) - (a + b)) (φ ⊗ₜ[F] (ψ ⊗ₜ[F] θ))) =
            homogeneousDualDegreeCast F (completionRootDegree (a + b))
              (homogeneousDualTensorConcat F (a + b)
                (2 ^ strictDyadicRoot (a + b) - (a + b))
                (homogeneousDualTensorConcat F a b (φ ⊗ₜ[F] ψ) ⊗ₜ[F] θ)) := by
            apply dualToAmbient_injective F _
            simp only [homogeneousDualTripleConcat, LinearEquiv.trans_apply,
              LinearEquiv.lTensor_tmul, dualToAmbient_degreeCast, dualToAmbient_tensorConcat]
            exact (mul_assoc _ _ _).symm
          rw [heq, actualRootPrefixContraction_tensorConcat_tmul,
            CriticalGK2.contractLast_tmul, map_smul]

/-- Actual root suffix contraction equals the actual aligned three-factor
suffix contraction, retaining a complete final block of length c. -/
theorem actualRootSuffixContraction_eq_actualSuffixContractionLeftAssociated (b c : ℕ)
    (η : Module.Dual F (HomogeneousDual F (2 ^ strictDyadicRoot (b + c) - (b + c))))
    (hdegree : ((2 ^ strictDyadicRoot (b + c) - (b + c)) + b) + c =
      2 ^ strictDyadicRoot (b + c))
    (z : HomogeneousDual F (((2 ^ strictDyadicRoot (b + c) - (b + c)) + b) + c)) :
    actualRootSuffixContraction F (b + c) η (homogeneousDualDegreeCast F hdegree z) =
      actualSuffixContractionLeftAssociated F (2 ^ strictDyadicRoot (b + c) - (b + c)) b c η z := by
  obtain ⟨w, rfl⟩ := (homogeneousDualTripleConcatLeft F
    (2 ^ strictDyadicRoot (b + c) - (b + c)) b c).surjective z
  simp only [actualSuffixContractionLeftAssociated, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  induction w using TensorProduct.induction_on with
  | zero =>
      rw [(homogeneousDualTripleConcatLeft F
          (2 ^ strictDyadicRoot (b + c) - (b + c)) b c).map_zero,
        (homogeneousDualDegreeCast F hdegree).map_zero,
        (actualRootSuffixContraction F (b + c) η).map_zero,
        (CriticalGK2.contractFirst η).map_zero,
        (homogeneousDualTensorConcat F b c).map_zero]
  | add u v hu hv =>
      rw [(homogeneousDualTripleConcatLeft F
          (2 ^ strictDyadicRoot (b + c) - (b + c)) b c).map_add,
        (homogeneousDualDegreeCast F hdegree).map_add,
        (actualRootSuffixContraction F (b + c) η).map_add,
        (CriticalGK2.contractFirst η).map_add,
        (homogeneousDualTensorConcat F b c).map_add, hu, hv]
  | tmul xy θ =>
      induction xy using TensorProduct.induction_on with
      | zero =>
          rw [TensorProduct.zero_tmul]
          rw [(homogeneousDualTripleConcatLeft F
              (2 ^ strictDyadicRoot (b + c) - (b + c)) b c).map_zero,
            (homogeneousDualDegreeCast F hdegree).map_zero,
            (actualRootSuffixContraction F (b + c) η).map_zero,
            (CriticalGK2.contractFirst η).map_zero,
            (homogeneousDualTensorConcat F b c).map_zero]
      | add u v hu hv =>
          simp only [add_tmul]
          rw [(homogeneousDualTripleConcatLeft F
              (2 ^ strictDyadicRoot (b + c) - (b + c)) b c).map_add,
            (homogeneousDualDegreeCast F hdegree).map_add,
            (actualRootSuffixContraction F (b + c) η).map_add,
            (CriticalGK2.contractFirst η).map_add,
            (homogeneousDualTensorConcat F b c).map_add, hu, hv]
      | tmul φ ψ =>
          have heq : homogeneousDualDegreeCast F hdegree
              (homogeneousDualTripleConcatLeft F
                (2 ^ strictDyadicRoot (b + c) - (b + c)) b c ((φ ⊗ₜ[F] ψ) ⊗ₜ[F] θ)) =
            homogeneousDualDegreeCast F (completionRootDegreeLeft (b + c))
              (homogeneousDualTensorConcat F
                (2 ^ strictDyadicRoot (b + c) - (b + c)) (b + c)
                (φ ⊗ₜ[F] homogeneousDualTensorConcat F b c (ψ ⊗ₜ[F] θ))) := by
            apply dualToAmbient_injective F _
            simp only [homogeneousDualTripleConcatLeft, LinearEquiv.trans_apply,
              LinearEquiv.rTensor_tmul, dualToAmbient_degreeCast, dualToAmbient_tensorConcat]
            exact mul_assoc _ _ _
          rw [heq, actualRootSuffixContraction_tensorConcat_tmul,
            CriticalGK2.contractFirst_tmul, map_smul]

/-- The prefix alignment degree is supplied by unconditional arithmetic. -/
theorem actualRootPrefixAlignmentDegree (a b : ℕ) :
    a + (b + (2 ^ strictDyadicRoot (a + b) - (a + b))) =
      2 ^ strictDyadicRoot (a + b) := by
  rw [← Nat.add_assoc]
  exact completionRootDegree (a + b)

/-- The suffix alignment degree is supplied by unconditional arithmetic. -/
theorem actualRootSuffixAlignmentDegree (b c : ℕ) :
    ((2 ^ strictDyadicRoot (b + c) - (b + c)) + b) + c =
      2 ^ strictDyadicRoot (b + c) := by
  rw [Nat.add_assoc]
  exact completionRootDegreeLeft (b + c)

end

end CriticalGK2.Actual
