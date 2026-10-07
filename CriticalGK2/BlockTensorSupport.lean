import CriticalGK2.DualWordBridge
import CriticalGK2.BlockPropagation
import CriticalGK2.LongCut

/-!
# Actual whole-block tensor support from polynomial block powers

This file identifies the inverse image of an actual dual tensor-product
subspace with genuine tensor support in its first or last complete factor.
The support conditions required by arbitrary whole-external contraction are
consequences of the actual polynomial block-power structure.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F : Type*) [Field F]

/-- The inverse of actual dual concatenation retains the complete first
included dual subspace. -/
theorem actualDualTensorProduct_first_support (a b : ℕ)
    (W : Submodule F (HomogeneousDual F a)) (T : Submodule F (HomogeneousDual F b)) :
    (actualDualTensorProduct F a b W T).map
        (homogeneousDualTensorConcat F a b).symm.toLinearMap ≤
      LinearMap.range (W.subtype.rTensor (HomogeneousDual F b)) := by
  rintro z ⟨φ, hφ, rfl⟩
  obtain ⟨w, ⟨v, rfl⟩, rfl⟩ := hφ
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  refine ⟨T.subtype.lTensor W v, ?_⟩
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul u v => simp

/-- The inverse of actual dual concatenation retains the complete last
included dual subspace. -/
theorem actualDualTensorProduct_last_support (a b : ℕ)
    (W : Submodule F (HomogeneousDual F a)) (T : Submodule F (HomogeneousDual F b)) :
    (actualDualTensorProduct F a b W T).map
        (homogeneousDualTensorConcat F a b).symm.toLinearMap ≤
      LinearMap.range (T.subtype.lTensor (HomogeneousDual F a)) := by
  rintro z ⟨φ, hφ, rfl⟩
  obtain ⟨w, ⟨v, rfl⟩, rfl⟩ := hφ
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  refine ⟨W.subtype.rTensor T v, ?_⟩
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul u v => simp

/-- A genuine actual block power also splits with its first block singled out. -/
theorem blockPower_left_split (S : Submodule F (WordAlgebra F)) (m : ℕ) :
    blockPower F S (m + 1) = productSpan F S (blockPower F S m) := by
  have h := (productSpan_blockPower F S 1 m).symm
  rw [blockPower_one] at h
  simpa only [Nat.add_comm] using h

/-- Actual complete first-block support for every nonempty polynomial block
power, expressed through the proved actual dual concatenation inverse. -/
theorem blockPower_first_support (S : Submodule F (WordAlgebra F)) (q : ℕ)
    (hS : S ≤ homogeneous F q) (m : ℕ) :
    (dualCoefficientSpace F (q + m * q) (blockPower F S (m + 1))).map
        (homogeneousDualTensorConcat F q (m * q)).symm.toLinearMap ≤
      LinearMap.range ((dualCoefficientSpace F q S).subtype.rTensor
        (HomogeneousDual F (m * q))) := by
  rw [blockPower_left_split]
  have h := dualCoefficientSpace_productSpan_le F q (m * q) S (blockPower F S m)
    hS (blockPower_le_homogeneous F S q hS m)
  exact (Submodule.map_mono h).trans
    (actualDualTensorProduct_first_support F q (m * q)
      (dualCoefficientSpace F q S) (dualCoefficientSpace F (m * q) (blockPower F S m)))

/-- The mirror complete last-block support for every nonempty polynomial
block power. -/
theorem blockPower_last_support (S : Submodule F (WordAlgebra F)) (q : ℕ)
    (hS : S ≤ homogeneous F q) (m : ℕ) :
    (dualCoefficientSpace F (m * q + q) (blockPower F S (m + 1))).map
        (homogeneousDualTensorConcat F (m * q) q).symm.toLinearMap ≤
      LinearMap.range ((dualCoefficientSpace F q S).subtype.lTensor
        (HomogeneousDual F (m * q))) := by
  rw [blockPower_succ]
  have h := dualCoefficientSpace_productSpan_le F (m * q) q (blockPower F S m) S
    (blockPower_le_homogeneous F S q hS m) hS
  exact (Submodule.map_mono h).trans
    (actualDualTensorProduct_last_support F (m * q) q
      (dualCoefficientSpace F (m * q) (blockPower F S m)) (dualCoefficientSpace F q S))

end

end CriticalGK2.Actual
