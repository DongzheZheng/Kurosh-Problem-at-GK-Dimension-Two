import CriticalGK2.WordTensorSuffix

/-! # Actual whole-exterior suffix contraction in dual word spaces -/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F : Type*) [Field F]

/-- Three actual dual word factors with left association. -/
def homogeneousDualTripleConcatLeft (a b c : ℕ) :
    (HomogeneousDual F a ⊗[F] HomogeneousDual F b) ⊗[F] HomogeneousDual F c ≃ₗ[F]
      HomogeneousDual F ((a + b) + c) :=
  (homogeneousDualTensorConcat F a b).rTensor (HomogeneousDual F c) ≪≫ₗ
    homogeneousDualTensorConcat F (a + b) c

/-- Retain the final two actual word factors and contract the whole first one. -/
def actualSuffixContractionLeftAssociated (a b c : ℕ)
    (η : Module.Dual F (HomogeneousDual F a)) :
    HomogeneousDual F ((a + b) + c) →ₗ[F] HomogeneousDual F (b + c) :=
  (homogeneousDualTensorConcat F b c).toLinearMap.comp
    ((CriticalGK2.contractFirst η).comp
      (homogeneousDualTripleConcatLeft F a b c).symm.toLinearMap)

/-- Actual dual triples with the complete final included word block. -/
def actualRightBlockTripleSpaceLeftAssociated (a b c : ℕ)
    (W : Submodule F (HomogeneousDual F c)) :
    Submodule F (HomogeneousDual F ((a + b) + c)) :=
  (LinearMap.range (W.subtype.lTensor (HomogeneousDual F a ⊗[F] HomogeneousDual F b))).map
    (homogeneousDualTripleConcatLeft F a b c).toLinearMap

/-- An arbitrary whole-exterior functional preserves the actual complete
suffix block. -/
theorem actualSuffixContractionLeftAssociated_mem (a b c : ℕ)
    (W : Submodule F (HomogeneousDual F c))
    (η : Module.Dual F (HomogeneousDual F a))
    (z : HomogeneousDual F ((a + b) + c))
    (hz : z ∈ actualRightBlockTripleSpaceLeftAssociated F a b c W) :
    actualSuffixContractionLeftAssociated F a b c η z ∈ actualRightBlockSpace F b c W := by
  obtain ⟨w, hw, rfl⟩ := hz
  change homogeneousDualTensorConcat F b c
    (CriticalGK2.contractFirst η
      ((homogeneousDualTripleConcatLeft F a b c).symm
        (homogeneousDualTripleConcatLeft F a b c w))) ∈ _
  rw [LinearEquiv.symm_apply_apply]
  exact ⟨CriticalGK2.contractFirst η w,
    CriticalGK2.contractFirst_mem_right_support W η w hw, rfl⟩

end

end CriticalGK2.Actual
