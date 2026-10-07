import CriticalGK2.WordTensor

/-!
# Actual suffix contractions

This is the mirror of the actual prefix connection in `WordTensor`.  Both
connections use the same proved actual word-space concatenation maps.
-/

namespace CriticalGK2.Actual

open TensorProduct

variable (F : Type*) [Field F]

/-- The actual three-block concatenation with left-associated input. -/
noncomputable def homogeneousDualTripleConcatLeftAssociated (a b c : ℕ) :
    (HomogeneousDual F a ⊗[F] HomogeneousDual F b) ⊗[F] HomogeneousDual F c ≃ₗ[F]
      HomogeneousDual F (a + (b + c)) :=
  TensorProduct.assoc F (HomogeneousDual F a) (HomogeneousDual F b)
    (HomogeneousDual F c) ≪≫ₗ homogeneousDualTripleConcat F a b c

/-- Contract the whole external first dual factor, retaining the suffix. -/
noncomputable def actualSuffixContraction (a b c : ℕ)
    (φ : Module.Dual F (HomogeneousDual F a)) :
    HomogeneousDual F (a + (b + c)) →ₗ[F] HomogeneousDual F (b + c) :=
  (homogeneousDualTensorConcat F b c).toLinearMap.comp
    ((CriticalGK2.contractFirst φ).comp
      (homogeneousDualTripleConcatLeftAssociated F a b c).symm.toLinearMap)

/-- Actual dual input space with its complete last W block. -/
noncomputable def actualRightBlockTripleSpace (a b c : ℕ)
    (W : Submodule F (HomogeneousDual F c)) :
    Submodule F (HomogeneousDual F (a + (b + c))) :=
  (LinearMap.range (W.subtype.lTensor (HomogeneousDual F a ⊗[F] HomogeneousDual F b))).map
    (homogeneousDualTripleConcatLeftAssociated F a b c).toLinearMap

/-- Actual retained dual space with its complete last W block. -/
noncomputable def actualRightBlockSpace (b c : ℕ)
    (W : Submodule F (HomogeneousDual F c)) :
    Submodule F (HomogeneousDual F (b + c)) :=
  (LinearMap.range (W.subtype.lTensor (HomogeneousDual F b))).map
    (homogeneousDualTensorConcat F b c).toLinearMap

/-- Arbitrary whole-external-space contraction preserves the complete W
block in the actual homogeneous dual suffix. -/
theorem actualSuffixContraction_mem (a b c : ℕ)
    (W : Submodule F (HomogeneousDual F c))
    (φ : Module.Dual F (HomogeneousDual F a))
    (z : HomogeneousDual F (a + (b + c)))
    (hz : z ∈ actualRightBlockTripleSpace F a b c W) :
    actualSuffixContraction F a b c φ z ∈ actualRightBlockSpace F b c W := by
  obtain ⟨w, hw, rfl⟩ := hz
  change homogeneousDualTensorConcat F b c
    (CriticalGK2.contractFirst φ
      ((homogeneousDualTripleConcatLeftAssociated F a b c).symm
        (homogeneousDualTripleConcatLeftAssociated F a b c w))) ∈ _
  rw [LinearEquiv.symm_apply_apply]
  exact ⟨CriticalGK2.contractFirst φ w,
    CriticalGK2.contractFirst_mem_right_support W φ w hw, rfl⟩

end CriticalGK2.Actual
