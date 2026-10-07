import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Annihilator readback after scalar extension

The scalar extension of a subspace is represented by the range of its
tensorized inclusion. Annihilator pairings characterize membership in this
range.

The proof works for an arbitrary vector space and coefficient module, so it
implies the manuscript's finite-dimensional statement for any commutative
coefficient algebra, including coefficient algebras with zero divisors.
-/

namespace CriticalGK2

open TensorProduct

section VectorSpaces

variable {F X C : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup C] [Module F C]

/-- Scalar extension of a linear functional: `x ⊗ c ↦ φ(x) • c`. -/
noncomputable def extendedPair (φ : Module.Dual F X) : X ⊗[F] C →ₗ[F] C :=
  (TensorProduct.lid F C).toLinearMap.comp (φ.rTensor C)

@[simp]
theorem extendedPair_tmul (φ : Module.Dual F X) (x : X) (c : C) :
    extendedPair φ (x ⊗ₜ[F] c) = φ x • c := by
  simp [extendedPair]

/-- The image of `D ⊗ C` under the tensorized inclusion in `X ⊗ C`. -/
def scalarExtension (D : Submodule F X) : Submodule F (X ⊗[F] C) :=
  LinearMap.range (D.subtype.rTensor C)

/-- Every annihilating functional vanishes on the scalar extension. -/
theorem extendedPair_eq_zero_of_mem_scalarExtension
    (D : Submodule F X) (z : X ⊗[F] C)
    (hz : z ∈ scalarExtension D) (φ : Module.Dual F X)
    (hφ : φ ∈ D.dualAnnihilator) : extendedPair φ z = 0 := by
  obtain ⟨w, rfl⟩ := hz
  have hkill : ∀ d : D, φ (d : X) = 0 := fun d =>
    (Submodule.mem_dualAnnihilator φ).mp hφ d d.property
  induction w using TensorProduct.induction_on with
  | zero => simp [extendedPair]
  | tmul d c => simp [hkill d]
  | add a b ha hb => simpa only [map_add, ha, hb, add_zero]

/-- Vanishing of all extended annihilator pairings detects the tensorized
subspace for any vector space and coefficient module. -/
theorem mem_scalarExtension_of_extendedPair_eq_zero
    (D : Submodule F X) (z : X ⊗[F] C)
    (hz : ∀ φ : Module.Dual F X, φ ∈ D.dualAnnihilator →
      extendedPair φ z = 0) : z ∈ scalarExtension D := by
  classical
  let b := Module.Free.chooseBasis F (X ⧸ D)
  have hq : D.mkQ.rTensor C z = 0 := by
    apply (TensorProduct.equivFinsuppOfBasisLeft (N := C) b).injective
    apply Finsupp.ext
    intro i
    rw [map_zero, Finsupp.zero_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply]
    have hφ : (b.coord i).comp D.mkQ ∈ D.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      have hmk : D.mkQ x = 0 :=
        (Submodule.Quotient.mk_eq_zero D).mpr hx
      simp [hmk]
    have hi := hz ((b.coord i).comp D.mkQ) hφ
    simpa only [extendedPair, LinearMap.comp_apply,
      LinearMap.rTensor_comp_apply] using hi
  change z ∈ LinearMap.range (D.subtype.rTensor C)
  rw [← rTensor_mkQ C D, LinearMap.mem_ker]
  exact hq

/-- The annihilator readback equivalence used at every homogeneous cut of
the manuscript. -/
theorem scalar_readback_iff (D : Submodule F X) (z : X ⊗[F] C) :
    (∀ φ : Module.Dual F X, φ ∈ D.dualAnnihilator →
      extendedPair φ z = 0) ↔ z ∈ scalarExtension D := by
  constructor
  · exact mem_scalarExtension_of_extendedPair_eq_zero D z
  · intro hz φ hφ
    exact extendedPair_eq_zero_of_mem_scalarExtension D z hz φ hφ

/-- Readback as an explicit lift, matching `z ∈ D ⊗ C` in the paper. -/
theorem scalar_readback_exists_lift (D : Submodule F X) (z : X ⊗[F] C) :
    (∀ φ : Module.Dual F X, φ ∈ D.dualAnnihilator →
      extendedPair φ z = 0) ↔
    ∃ w : D ⊗[F] C, D.subtype.rTensor C w = z := by
  exact scalar_readback_iff D z

/-- Equivalent quotient formulation: all annihilator pairings vanish
precisely when the image of the element in `(X/D) ⊗ C` is zero. -/
theorem scalar_readback_quotient_iff (D : Submodule F X) (z : X ⊗[F] C) :
    (∀ φ : Module.Dual F X, φ ∈ D.dualAnnihilator →
      extendedPair φ z = 0) ↔ D.mkQ.rTensor C z = 0 := by
  rw [scalar_readback_iff]
  change z ∈ LinearMap.range (D.subtype.rTensor C) ↔ _
  rw [← rTensor_mkQ C D, LinearMap.mem_ker]

end VectorSpaces

section CoefficientAlgebras

variable {F X C : Type*} [Field F]
  [AddCommGroup X] [Module F X] [CommRing C] [Algebra F C]

/-- In a coefficient algebra, the extended pairing is exactly the pairing
obtained by replacing the scalar value of a functional by its image under
the structure map and multiplying by the coefficient. -/
@[simp]
theorem extendedPair_algebra_tmul (φ : Module.Dual F X) (x : X) (c : C) :
    extendedPair φ (x ⊗ₜ[F] c) = algebraMap F C (φ x) * c := by
  rw [extendedPair_tmul, Algebra.smul_def]

end CoefficientAlgebras

end CriticalGK2
