import CriticalGK2.LongCut
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Honest contraction ranks and fixed tensor augmentation

The maps in this module are the actual full functional contractions of a
tensor. In particular, their ranges quantify over every functional on the
entire discarded factor. Fixed nonzero factors preserve these ranges, or
transport them through injective tensor maps.
-/

namespace CriticalGK2.ContractionBudget

noncomputable section

open TensorProduct

variable {F X Y Z : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]
  [AddCommGroup Z] [Module F Z]

/-- The actual map `eta ↦ (id ⊗ eta)(t)`. Its range is the complete prefix
contraction support of the single tensor. -/
def leftFlattening (t : X ⊗[F] Y) : Module.Dual F Y →ₗ[F] X where
  toFun eta := contractRight eta t
  map_add' eta theta := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]; abel
    | tmul x y => simp [add_smul]
  map_smul' c eta := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, smul_add]
    | tmul x y => simp [smul_smul]

/-- The actual transpose flattening `phi ↦ (phi ⊗ id)(t)`. -/
def rightFlattening (t : X ⊗[F] Y) : Module.Dual F X →ₗ[F] Y where
  toFun phi := extendedPair phi t
  map_add' phi psi := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]; abel
    | tmul x y => simp [add_smul]
  map_smul' c phi := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, smul_add]
    | tmul x y => simp [smul_smul]

@[simp] theorem leftFlattening_apply (t : X ⊗[F] Y) (eta : Module.Dual F Y) :
    leftFlattening t eta = contractRight eta t := rfl

@[simp] theorem rightFlattening_apply (t : X ⊗[F] Y) (phi : Module.Dual F X) :
    rightFlattening t phi = extendedPair phi t := rfl

/-- The complete cut rank, computed from an actual range. -/
def tensorCutRank (t : X ⊗[F] Y) : ℕ :=
  Module.finrank F (LinearMap.range (leftFlattening t))

/-- Tensoring on the right with a fixed vector, as an actual linear map. -/
def fixedRightMap (z : Z) : Y →ₗ[F] Y ⊗[F] Z where
  toFun y := y ⊗ₜ[F] z
  map_add' _ _ := add_tmul _ _ _
  map_smul' _ _ := (smul_tmul' _ _ _).symm

@[simp] theorem fixedRightMap_apply (z : Z) (y : Y) :
    fixedRightMap z y = y ⊗ₜ[F] z := rfl

/-- An arbitrary functional on `Y ⊗ Z`, specialized only after fixing `z`.
The input functional may mix the whole discarded factor. -/
def specializeRight (z : Z) (eta : Module.Dual F (Y ⊗[F] Z)) : Module.Dual F Y :=
  eta.comp (fixedRightMap z)

@[simp] theorem specializeRight_apply (z : Z)
    (eta : Module.Dual F (Y ⊗[F] Z)) (y : Y) :
    specializeRight z eta y = eta (y ⊗ₜ[F] z) := rfl

/-- Honest full contraction after attaching a fixed last factor. -/
theorem leftFlattening_append_apply (t : X ⊗[F] Y) (z : Z)
    (eta : Module.Dual F (Y ⊗[F] Z)) :
    leftFlattening (TensorProduct.assoc F X Y Z (t ⊗ₜ[F] z)) eta =
      leftFlattening t (specializeRight z eta) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
      simp only [leftFlattening_apply] at ha hb
      simp only [add_tmul, map_add, leftFlattening_apply, ha, hb]
  | tmul x y => simp only [TensorProduct.assoc_tmul, leftFlattening_apply,
      contractRight_tmul, specializeRight_apply]

/-- Nonzero fixed factors allow every functional on `Y` to be recovered
from a functional on the whole actual factor `Y ⊗ Z`. -/
theorem specializeRight_surjective (z : Z) (hz : z ≠ 0) :
    Function.Surjective (specializeRight (F := F) (Y := Y) z) := by
  obtain ⟨psi, hpsi⟩ := Module.Projective.exists_dual_eq_one F hz
  intro eta
  refine ⟨eta.comp (contractRight psi), ?_⟩
  ext y
  simp only [specializeRight_apply, LinearMap.comp_apply, contractRight_tmul,
    hpsi, one_smul]

/-- Appending a fixed nonzero tensor factor preserves the complete prefix
support itself, including functionals mixing all outside coordinates. -/
theorem leftFlattening_append_range (t : X ⊗[F] Y) (z : Z) (hz : z ≠ 0) :
    LinearMap.range (leftFlattening (TensorProduct.assoc F X Y Z (t ⊗ₜ[F] z))) =
      LinearMap.range (leftFlattening t) := by
  apply le_antisymm
  · rintro x ⟨eta, rfl⟩
    exact ⟨specializeRight z eta, (leftFlattening_append_apply t z eta).symm⟩
  · rintro x ⟨eta, rfl⟩
    obtain ⟨theta, htheta⟩ := specializeRight_surjective z hz eta
    exact ⟨theta, by rw [leftFlattening_append_apply, htheta]⟩

/-- Consequently the actual cut rank is unchanged. -/
theorem tensorCutRank_append (t : X ⊗[F] Y) (z : Z) (hz : z ≠ 0) :
    tensorCutRank (TensorProduct.assoc F X Y Z (t ⊗ₜ[F] z)) = tensorCutRank t := by
  unfold tensorCutRank
  rw [leftFlattening_append_range t z hz]

/-- Honest full contraction after attaching a fixed first factor. -/
theorem leftFlattening_prepend_apply (z : Z) (t : X ⊗[F] Y)
    (eta : Module.Dual F Y) :
    leftFlattening ((TensorProduct.assoc F Z X Y).symm (z ⊗ₜ[F] t)) eta =
      z ⊗ₜ[F] leftFlattening t eta := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
      simp only [leftFlattening_apply] at ha hb
      simp only [tmul_add, map_add, leftFlattening_apply, ha, hb]
  | tmul x y =>
      simp only [TensorProduct.assoc_symm_tmul, leftFlattening_apply,
        contractRight_tmul, tmul_smul]

/-- The actual prefix support after a fixed first factor is the image
under the actual fixed-left tensor map. -/
theorem leftFlattening_prepend_range (z : Z) (t : X ⊗[F] Y) :
    LinearMap.range
        (leftFlattening ((TensorProduct.assoc F Z X Y).symm (z ⊗ₜ[F] t))) =
      (LinearMap.range (leftFlattening t)).map (TensorProduct.mk F Z X z) := by
  apply le_antisymm
  · rintro x ⟨eta, rfl⟩
    exact ⟨leftFlattening t eta, ⟨eta, rfl⟩,
      (leftFlattening_prepend_apply z t eta).symm⟩
  · rintro x ⟨y, ⟨eta, rfl⟩, rfl⟩
    exact ⟨eta, leftFlattening_prepend_apply z t eta⟩

/-- Finrank is preserved under an injective linear map, by restricting the
map to the given subspace. -/
theorem finrank_map_of_injective {A B : Type*} [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B] (f : A →ₗ[F] B) (hf : Function.Injective f)
    (S : Submodule F A) : Module.finrank F (S.map f) = Module.finrank F S := by
  have hg : Function.Injective (f.comp S.subtype) := hf.comp Subtype.val_injective
  have he : LinearMap.range (f.comp S.subtype) = S.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← he]
  exact LinearMap.finrank_range_of_inj hg

/-- Prepending a fixed nonzero factor preserves the actual cut rank,
although the retained support lives in a larger actual ambient space. -/
theorem tensorCutRank_prepend (z : Z) (hz : z ≠ 0) (t : X ⊗[F] Y) :
    tensorCutRank ((TensorProduct.assoc F Z X Y).symm (z ⊗ₜ[F] t)) =
      tensorCutRank t := by
  unfold tensorCutRank
  rw [leftFlattening_prepend_range]
  exact finrank_map_of_injective (TensorProduct.mk F Z X z)
    (fixed_left_tensor_injective z hz) (LinearMap.range (leftFlattening t))

/-- Actual transport of the retained factor transports the entire range. -/
theorem leftFlattening_leftEquiv_range {A : Type*} [AddCommGroup A] [Module F A]
    (e : X ≃ₗ[F] A) (t : X ⊗[F] Y) :
    LinearMap.range (leftFlattening (e.rTensor Y t)) =
      (LinearMap.range (leftFlattening t)).map e.toLinearMap := by
  have heval : ∀ eta : Module.Dual F Y,
      leftFlattening (e.rTensor Y t) eta = e (leftFlattening t eta) := by
    intro eta
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
        simp only [leftFlattening_apply] at ha hb
        simp only [map_add, leftFlattening_apply, ha, hb]
    | tmul x y => simp only [LinearEquiv.rTensor_tmul, leftFlattening_apply,
        contractRight_tmul, map_smul]
  apply le_antisymm
  · rintro x ⟨eta, rfl⟩
    exact ⟨leftFlattening t eta, ⟨eta, rfl⟩, (heval eta).symm⟩
  · rintro x ⟨y, ⟨eta, rfl⟩, rfl⟩
    exact ⟨eta, heval eta⟩

/-- Actual transport of the discarded factor leaves complete support
unchanged; functionals are transported through the inverse equivalence. -/
theorem leftFlattening_rightEquiv_range {A : Type*} [AddCommGroup A] [Module F A]
    (e : Y ≃ₗ[F] A) (t : X ⊗[F] Y) :
    LinearMap.range (leftFlattening (e.lTensor X t)) =
      LinearMap.range (leftFlattening t) := by
  have heval : ∀ eta : Module.Dual F A,
      leftFlattening (e.lTensor X t) eta = leftFlattening t (eta.comp e.toLinearMap) := by
    intro eta
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
        simp only [leftFlattening_apply] at ha hb
        simp only [map_add, leftFlattening_apply, ha, hb]
    | tmul x y => simp only [LinearEquiv.lTensor_tmul, leftFlattening_apply,
        contractRight_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe]
  apply le_antisymm
  · rintro x ⟨eta, rfl⟩
    exact ⟨eta.comp e.toLinearMap, (heval eta).symm⟩
  · rintro x ⟨eta, rfl⟩
    refine ⟨eta.comp e.symm.toLinearMap, ?_⟩
    rw [heval]
    congr 1
    ext y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem tensorCutRank_leftEquiv {A : Type*} [AddCommGroup A] [Module F A]
    (e : X ≃ₗ[F] A) (t : X ⊗[F] Y) :
    tensorCutRank (e.rTensor Y t) = tensorCutRank t := by
  unfold tensorCutRank
  rw [leftFlattening_leftEquiv_range]
  exact e.finrank_map_eq (LinearMap.range (leftFlattening t))

theorem tensorCutRank_rightEquiv {A : Type*} [AddCommGroup A] [Module F A]
    (e : Y ≃ₗ[F] A) (t : X ⊗[F] Y) :
    tensorCutRank (e.lTensor X t) = tensorCutRank t := by
  unfold tensorCutRank
  rw [leftFlattening_rightEquiv_range]

/-- The two honest flattenings are actual transposes, through the finite
evaluation equivalence. Thus complete suffix and prefix cut ranks agree. -/
theorem rightFlattening_finrank_eq_left [FiniteDimensional F X] [FiniteDimensional F Y]
    (t : X ⊗[F] Y) :
    Module.finrank F (LinearMap.range (rightFlattening t)) = tensorCutRank t := by
  have htranspose : (Module.evalEquiv F Y).toLinearMap.comp (rightFlattening t) =
      (leftFlattening t).dualMap := by
    ext phi eta
    change eta (extendedPair phi t) = phi (contractRight eta t)
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul x y => simp only [extendedPair_tmul, contractRight_tmul, map_smul,
        smul_eq_mul, mul_comm]
  calc
    Module.finrank F (LinearMap.range (rightFlattening t)) =
        Module.finrank F ((LinearMap.range (rightFlattening t)).map
          (Module.evalEquiv F Y).toLinearMap) :=
      ((Module.evalEquiv F Y).finrank_map_eq (LinearMap.range (rightFlattening t))).symm
    _ = Module.finrank F (LinearMap.range ((leftFlattening t).dualMap)) := by
      rw [← LinearMap.range_comp, htranspose]
    _ = tensorCutRank t := LinearMap.finrank_range_dualMap_eq_finrank_range _

#print axioms CriticalGK2.ContractionBudget.tensorCutRank_append
#print axioms CriticalGK2.ContractionBudget.tensorCutRank_prepend

end

end CriticalGK2.ContractionBudget
