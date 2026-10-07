import CriticalGK2.ScalarReadback
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Whole external contraction preserves a complete block

The external space is an arbitrary vector space. The contraction theorem
allows every functional on this entire space, including functionals that
mix all outside positions. It gives the linear-algebra connection in
`prop:nil-readback`.

The input is membership in the actual tensorized image of the complete
block subspace, before contraction.  Support after contraction is proved.
Evaluation vanishes when the complete block subspace lies in the kernel of
the actual linear block-evaluation map.
-/

namespace CriticalGK2

open TensorProduct

section Contractions

variable {F X Y Z : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]
  [AddCommGroup Z] [Module F Z]

/-- Contract the entire right tensor factor by an arbitrary functional. -/
noncomputable def contractRight (φ : Module.Dual F Y) : X ⊗[F] Y →ₗ[F] X :=
  (TensorProduct.rid F X).toLinearMap.comp (φ.lTensor X)

@[simp]
theorem contractRight_tmul (φ : Module.Dual F Y) (x : X) (y : Y) :
    contractRight φ (x ⊗ₜ[F] y) = φ y • x := by
  simp [contractRight]

/-- A fixed nonzero right factor gives an injection, proved by choosing
a functional which takes value one on that factor. -/
theorem fixed_right_tensor_injective (y : Y) (hy : y ≠ 0) :
    Function.Injective (fun x : X => x ⊗ₜ[F] y) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hy
  intro x₁ x₂ h
  have hc := congrArg (contractRight φ) h
  simpa [hφ] using hc

/-- The mirror injection for a fixed nonzero left tensor factor. -/
theorem fixed_left_tensor_injective (x : X) (hx : x ≠ 0) :
    Function.Injective (fun y : Y => x ⊗ₜ[F] y) := by
  intro y₁ y₂ h
  apply fixed_right_tensor_injective (F := F) (X := Y) (Y := X) x hx
  have hc := congrArg (TensorProduct.comm F X Y) h
  simpa only [TensorProduct.comm_tmul] using hc

/-- Retain the first two factors and contract the entire last factor. -/
noncomputable def contractLast (φ : Module.Dual F Z) :
    X ⊗[F] (Y ⊗[F] Z) →ₗ[F] X ⊗[F] Y :=
  (contractRight φ).comp (TensorProduct.assoc F X Y Z).symm.toLinearMap

@[simp]
theorem contractLast_tmul (φ : Module.Dual F Z) (x : X) (y : Y) (z : Z) :
    contractLast φ (x ⊗ₜ[F] (y ⊗ₜ[F] z)) = φ z • (x ⊗ₜ[F] y) := by
  simp [contractLast]

/-- Naturality with the actual inclusion of the complete first block. -/
theorem contractLast_inclusion (W : Submodule F X) (φ : Module.Dual F Z)
    (w : W ⊗[F] (Y ⊗[F] Z)) :
    contractLast φ (W.subtype.rTensor (Y ⊗[F] Z) w) =
      W.subtype.rTensor Y (contractLast φ w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v yz =>
    induction yz using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
    | tmul y z => simp

/-- Complete first-block support survives arbitrary contraction of the
whole outside factor. -/
theorem contractLast_mem_left_support (W : Submodule F X)
    (φ : Module.Dual F Z) (z : X ⊗[F] (Y ⊗[F] Z))
    (hz : z ∈ LinearMap.range (W.subtype.rTensor (Y ⊗[F] Z))) :
    contractLast φ z ∈ LinearMap.range (W.subtype.rTensor Y) := by
  obtain ⟨w, hw⟩ := hz
  refine ⟨contractLast φ w, ?_⟩
  rw [← contractLast_inclusion]
  exact congrArg (contractLast φ) hw

/-- Retain the last two factors and contract the entire first factor. -/
noncomputable def contractFirst (φ : Module.Dual F X) :
    (X ⊗[F] Y) ⊗[F] Z →ₗ[F] Y ⊗[F] Z :=
  (extendedPair φ).comp (TensorProduct.assoc F X Y Z).toLinearMap

@[simp]
theorem contractFirst_tmul (φ : Module.Dual F X) (x : X) (y : Y) (z : Z) :
    contractFirst φ ((x ⊗ₜ[F] y) ⊗ₜ[F] z) = φ x • (y ⊗ₜ[F] z) := by
  simp [contractFirst]

/-- Naturality with the actual inclusion of the complete last block. -/
theorem contractFirst_inclusion (W : Submodule F Z) (φ : Module.Dual F X)
    (w : (X ⊗[F] Y) ⊗[F] W) :
    contractFirst φ (W.subtype.lTensor (X ⊗[F] Y) w) =
      W.subtype.lTensor Y (contractFirst φ w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul xy v =>
    induction xy using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [add_tmul, map_add, ha, hb]
    | tmul x y => simp

/-- Complete last-block support survives arbitrary contraction of the
whole outside factor. -/
theorem contractFirst_mem_right_support (W : Submodule F Z)
    (φ : Module.Dual F X) (z : (X ⊗[F] Y) ⊗[F] Z)
    (hz : z ∈ LinearMap.range (W.subtype.lTensor (X ⊗[F] Y))) :
    contractFirst φ z ∈ LinearMap.range (W.subtype.lTensor Y) := by
  obtain ⟨w, hw⟩ := hz
  refine ⟨contractFirst φ w, ?_⟩
  rw [← contractFirst_inclusion]
  exact congrArg (contractFirst φ) hw

/-- Linear span of all contractions by arbitrary whole-external-space
functionals.  The supremum of images implements that span as a submodule. -/
noncomputable def fullPrefixContractionSupport
    (S : Submodule F (X ⊗[F] (Y ⊗[F] Z))) : Submodule F (X ⊗[F] Y) :=
  ⨆ φ : Module.Dual F Z, S.map (contractLast φ)

/-- The whole prefix contraction support retains the complete first block. -/
theorem fullPrefixContractionSupport_le (W : Submodule F X)
    (S : Submodule F (X ⊗[F] (Y ⊗[F] Z)))
    (hS : S ≤ LinearMap.range (W.subtype.rTensor (Y ⊗[F] Z))) :
    fullPrefixContractionSupport S ≤ LinearMap.range (W.subtype.rTensor Y) := by
  refine iSup_le fun φ => ?_
  rintro z ⟨w, hw, rfl⟩
  exact contractLast_mem_left_support W φ w (hS hw)

/-- The corresponding span for arbitrary whole-external-space suffix
contractions. -/
noncomputable def fullSuffixContractionSupport
    (S : Submodule F ((X ⊗[F] Y) ⊗[F] Z)) : Submodule F (Y ⊗[F] Z) :=
  ⨆ φ : Module.Dual F X, S.map (contractFirst φ)

/-- The whole suffix contraction support retains the complete last block. -/
theorem fullSuffixContractionSupport_le (W : Submodule F Z)
    (S : Submodule F ((X ⊗[F] Y) ⊗[F] Z))
    (hS : S ≤ LinearMap.range (W.subtype.lTensor (X ⊗[F] Y))) :
    fullSuffixContractionSupport S ≤ LinearMap.range (W.subtype.lTensor Y) := by
  refine iSup_le fun φ => ?_
  rintro z ⟨w, hw, rfl⟩
  exact contractFirst_mem_right_support W φ w (hS hw)

end Contractions

section Evaluation

variable {F X Y Z A B T : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]
  [AddCommGroup Z] [Module F Z]
  [AddCommGroup A] [Module F A]
  [AddCommGroup B] [Module F B]
  [AddCommGroup T] [Module F T]

/-- Evaluation through the actual block maps and an actual bilinear
composition operation, such as matrix multiplication. -/
noncomputable def evaluatePair (f : X →ₗ[F] A) (g : Y →ₗ[F] B)
    (mul : A →ₗ[F] B →ₗ[F] T) : X ⊗[F] Y →ₗ[F] T :=
  (TensorProduct.lift mul).comp (TensorProduct.map f g)

@[simp]
theorem evaluatePair_tmul (f : X →ₗ[F] A) (g : Y →ₗ[F] B)
    (mul : A →ₗ[F] B →ₗ[F] T) (x : X) (y : Y) :
    evaluatePair f g mul (x ⊗ₜ[F] y) = mul (f x) (g y) := by
  simp [evaluatePair]

/-- A zero evaluated left block forces zero for every supported tensor. -/
theorem evaluatePair_eq_zero_of_left_support
    (W : Submodule F X) (f : X →ₗ[F] A) (g : Y →ₗ[F] B)
    (mul : A →ₗ[F] B →ₗ[F] T) (hW : W ≤ LinearMap.ker f)
    (z : X ⊗[F] Y) (hz : z ∈ LinearMap.range (W.subtype.rTensor Y)) :
    evaluatePair f g mul z = 0 := by
  obtain ⟨w, rfl⟩ := hz
  have hkill : ∀ v : W, f (v : X) = 0 := fun v => hW v.property
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | tmul v y => simp [hkill v]

/-- A zero evaluated right block forces zero for every supported tensor. -/
theorem evaluatePair_eq_zero_of_right_support
    (W : Submodule F Y) (f : X →ₗ[F] A) (g : Y →ₗ[F] B)
    (mul : A →ₗ[F] B →ₗ[F] T) (hW : W ≤ LinearMap.ker g)
    (z : X ⊗[F] Y) (hz : z ∈ LinearMap.range (W.subtype.lTensor X)) :
    evaluatePair f g mul z = 0 := by
  obtain ⟨w, rfl⟩ := hz
  have hkill : ∀ v : W, g (v : Y) = 0 := fun v => hW v.property
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | tmul x v => simp [hkill v]

/-- The complete prefix block remains an evaluated zero block after an
arbitrary contraction of all outside positions. -/
theorem long_prefix_contraction_evaluation_eq_zero
    (W : Submodule F X) (f : X →ₗ[F] A) (g : Y →ₗ[F] B)
    (mul : A →ₗ[F] B →ₗ[F] T) (hW : W ≤ LinearMap.ker f)
    (φ : Module.Dual F Z) (z : X ⊗[F] (Y ⊗[F] Z))
    (hz : z ∈ LinearMap.range (W.subtype.rTensor (Y ⊗[F] Z))) :
    evaluatePair f g mul (contractLast φ z) = 0 := by
  exact evaluatePair_eq_zero_of_left_support W f g mul hW _
    (contractLast_mem_left_support W φ z hz)

/-- The mirror statement for a complete suffix zero block. -/
theorem long_suffix_contraction_evaluation_eq_zero
    (W : Submodule F Z) (f : Y →ₗ[F] A) (g : Z →ₗ[F] B)
    (mul : A →ₗ[F] B →ₗ[F] T) (hW : W ≤ LinearMap.ker g)
    (φ : Module.Dual F X) (z : (X ⊗[F] Y) ⊗[F] Z)
    (hz : z ∈ LinearMap.range (W.subtype.lTensor (X ⊗[F] Y))) :
    evaluatePair f g mul (contractFirst φ z) = 0 := by
  exact evaluatePair_eq_zero_of_right_support W f g mul hW _
    (contractFirst_mem_right_support W φ z hz)

/-- Zero evaluation of the full prefix contraction support, including
linear combinations of contractions by different external functionals. -/
theorem fullPrefixContractionSupport_le_evaluation_kernel
    (W : Submodule F X) (f : X →ₗ[F] A) (g : Y →ₗ[F] B)
    (mul : A →ₗ[F] B →ₗ[F] T) (hW : W ≤ LinearMap.ker f)
    (S : Submodule F (X ⊗[F] (Y ⊗[F] Z)))
    (hS : S ≤ LinearMap.range (W.subtype.rTensor (Y ⊗[F] Z))) :
    fullPrefixContractionSupport S ≤ LinearMap.ker (evaluatePair f g mul) := by
  intro z hz
  exact evaluatePair_eq_zero_of_left_support W f g mul hW z
    (fullPrefixContractionSupport_le W S hS hz)

/-- Zero evaluation of the full suffix contraction support. -/
theorem fullSuffixContractionSupport_le_evaluation_kernel
    (W : Submodule F Z) (f : Y →ₗ[F] A) (g : Z →ₗ[F] B)
    (mul : A →ₗ[F] B →ₗ[F] T) (hW : W ≤ LinearMap.ker g)
    (S : Submodule F ((X ⊗[F] Y) ⊗[F] Z))
    (hS : S ≤ LinearMap.range (W.subtype.lTensor (X ⊗[F] Y))) :
    fullSuffixContractionSupport S ≤ LinearMap.ker (evaluatePair f g mul) := by
  intro z hz
  exact evaluatePair_eq_zero_of_right_support W f g mul hW z
    (fullSuffixContractionSupport_le W S hS hz)

end Evaluation

end CriticalGK2
