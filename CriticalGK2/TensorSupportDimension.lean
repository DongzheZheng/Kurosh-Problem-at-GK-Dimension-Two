import CriticalGK2.FreeTailCutSupport
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Full arbitrary-functional support dimensions

The supremum over all contractions is the range of one actual bilinear
contraction map on `S ⊗ Dual(exterior)`. This proves the dimension bound and
includes scalar exterior endpoint cuts.
-/

namespace CriticalGK2.ContractionBudget

noncomputable section

open TensorProduct

variable {F X Y : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]

def subspacePrefixBilinear (S : Submodule F (X ⊗[F] Y)) :
    S →ₗ[F] Module.Dual F Y →ₗ[F] X where
  toFun s := leftFlattening s.val
  map_add' a b := by
    ext eta
    change contractRight eta (a.val + b.val) = contractRight eta a.val + contractRight eta b.val
    exact (contractRight eta).map_add a.val b.val
  map_smul' c a := by
    ext eta
    change contractRight eta (c • a.val) = c • contractRight eta a.val
    exact (contractRight eta).map_smul c a.val

def subspaceSuffixBilinear (S : Submodule F (X ⊗[F] Y)) :
    S →ₗ[F] Module.Dual F X →ₗ[F] Y where
  toFun s := rightFlattening s.val
  map_add' a b := by
    ext phi
    change extendedPair phi (a.val + b.val) = extendedPair phi a.val + extendedPair phi b.val
    exact (extendedPair phi).map_add a.val b.val
  map_smul' c a := by
    ext phi
    change extendedPair phi (c • a.val) = c • extendedPair phi a.val
    exact (extendedPair phi).map_smul c a.val

theorem tensorPrefixSupport_eq_bilinear_range (S : Submodule F (X ⊗[F] Y)) :
    tensorPrefixSupport S = LinearMap.range (TensorProduct.lift (subspacePrefixBilinear S)) := by
  apply le_antisymm
  · refine iSup_le fun eta => ?_
    rintro x ⟨s, hs, rfl⟩
    exact ⟨(⟨s, hs⟩ : S) ⊗ₜ[F] eta, rfl⟩
  · rintro x ⟨u, rfl⟩
    induction u using TensorProduct.induction_on with
    | zero =>
        rw [(TensorProduct.lift (subspacePrefixBilinear S)).map_zero]
        exact Submodule.zero_mem _
    | add a b ha hb =>
        rw [(TensorProduct.lift (subspacePrefixBilinear S)).map_add]
        exact Submodule.add_mem _ ha hb
    | tmul s eta =>
        exact contractRight_mem_tensorPrefixSupport S eta s.val s.property

theorem tensorSuffixSupport_eq_bilinear_range (S : Submodule F (X ⊗[F] Y)) :
    tensorSuffixSupport S = LinearMap.range (TensorProduct.lift (subspaceSuffixBilinear S)) := by
  apply le_antisymm
  · refine iSup_le fun phi => ?_
    rintro x ⟨s, hs, rfl⟩
    exact ⟨(⟨s, hs⟩ : S) ⊗ₜ[F] phi, rfl⟩
  · rintro x ⟨u, rfl⟩
    induction u using TensorProduct.induction_on with
    | zero =>
        rw [(TensorProduct.lift (subspaceSuffixBilinear S)).map_zero]
        exact Submodule.zero_mem _
    | add a b ha hb =>
        rw [(TensorProduct.lift (subspaceSuffixBilinear S)).map_add]
        exact Submodule.add_mem _ ha hb
    | tmul s phi =>
        exact extendedPair_mem_tensorSuffixSupport S phi s.val s.property

theorem tensorPrefixSupport_finrank_le [FiniteDimensional F X] [FiniteDimensional F Y]
    (S : Submodule F (X ⊗[F] Y)) :
    Module.finrank F (tensorPrefixSupport S) ≤ Module.finrank F S * Module.finrank F Y := by
  letI : Module.Free F S := Module.Free.of_basis (Module.Basis.ofVectorSpace F S)
  letI : Module.Free F (Module.Dual F Y) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace F (Module.Dual F Y))
  rw [tensorPrefixSupport_eq_bilinear_range]
  calc
    Module.finrank F (LinearMap.range (TensorProduct.lift (subspacePrefixBilinear S))) ≤
        Module.finrank F (S ⊗[F] Module.Dual F Y) := LinearMap.finrank_range_le _
    _ = Module.finrank F S * Module.finrank F Y := by
      rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq]

theorem tensorSuffixSupport_finrank_le [FiniteDimensional F X] [FiniteDimensional F Y]
    (S : Submodule F (X ⊗[F] Y)) :
    Module.finrank F (tensorSuffixSupport S) ≤ Module.finrank F S * Module.finrank F X := by
  letI : Module.Free F S := Module.Free.of_basis (Module.Basis.ofVectorSpace F S)
  letI : Module.Free F (Module.Dual F X) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace F (Module.Dual F X))
  rw [tensorSuffixSupport_eq_bilinear_range]
  calc
    Module.finrank F (LinearMap.range (TensorProduct.lift (subspaceSuffixBilinear S))) ≤
        Module.finrank F (S ⊗[F] Module.Dual F X) := LinearMap.finrank_range_le _
    _ = Module.finrank F S * Module.finrank F X := by
      rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq]

#print axioms CriticalGK2.ContractionBudget.tensorPrefixSupport_finrank_le

end

end CriticalGK2.ContractionBudget
