import CriticalGK2.FreeTailCutSupport
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Whole-cut support bounds inside the second tensor block

The tensor product consists of an actual first space S and an actual second
space T with an internal cut. Prefix support lies in the included tensor
product of S with the prefix support of T. Suffix support lies in the old
suffix support of T. All discarded-factor functionals are arbitrary whole
functionals; specialization occurs only after fixing a first-factor vector.
-/

namespace CriticalGK2.ContractionBudget

noncomputable section

open TensorProduct

variable {F X Y Z : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]
  [AddCommGroup Z] [Module F Z]

variable {A : Type*} [AddCommGroup A] [Module F A]

theorem contractRight_leftEquiv (e : X ≃ₗ[F] A) (t : X ⊗[F] Y)
    (eta : Module.Dual F Y) :
    contractRight eta (e.rTensor Y t) = e (contractRight eta t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul x y =>
      simp only [LinearEquiv.rTensor_tmul, contractRight_tmul, map_smul]

theorem extendedPair_leftEquiv (e : X ≃ₗ[F] A) (t : X ⊗[F] Y)
    (phi : Module.Dual F A) :
    extendedPair phi (e.rTensor Y t) = extendedPair (phi.comp e.toLinearMap) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul x y =>
      simp only [LinearEquiv.rTensor_tmul, extendedPair_tmul,
        LinearMap.comp_apply, LinearEquiv.coe_coe]

/-- Retained-factor transport identifies the complete prefix support with
the corresponding subspace image. -/
theorem tensorPrefixSupport_leftEquiv (e : X ≃ₗ[F] A)
    (S : Submodule F (X ⊗[F] Y)) :
    tensorPrefixSupport (S.map (e.rTensor Y).toLinearMap) =
      (tensorPrefixSupport S).map e.toLinearMap := by
  apply le_antisymm
  · refine iSup_le fun eta => ?_
    rintro x ⟨u, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨contractRight eta t, contractRight_mem_tensorPrefixSupport S eta t ht, ?_⟩
    change e (contractRight eta t) = contractRight eta (e.rTensor Y t)
    exact (contractRight_leftEquiv e t eta).symm
  · rw [Submodule.map_le_iff_le_comap]
    refine iSup_le fun eta => ?_
    rintro x ⟨t, ht, rfl⟩
    have hu : e.rTensor Y t ∈ S.map (e.rTensor Y).toLinearMap := ⟨t, ht, rfl⟩
    have hc := contractRight_mem_tensorPrefixSupport
      (S.map (e.rTensor Y).toLinearMap) eta _ hu
    change e (contractRight eta t) ∈ tensorPrefixSupport (S.map (e.rTensor Y).toLinearMap)
    rw [← contractRight_leftEquiv e t eta]
    exact hc

/-- Functionals on the transported discarded factor are pulled back through
the equivalence and its inverse, so actual suffix support is unchanged. -/
theorem tensorSuffixSupport_leftEquiv (e : X ≃ₗ[F] A)
    (S : Submodule F (X ⊗[F] Y)) :
    tensorSuffixSupport (S.map (e.rTensor Y).toLinearMap) = tensorSuffixSupport S := by
  apply le_antisymm
  · refine iSup_le fun phi => ?_
    rintro x ⟨u, ⟨t, ht, rfl⟩, rfl⟩
    change extendedPair phi (e.rTensor Y t) ∈ tensorSuffixSupport S
    rw [extendedPair_leftEquiv]
    exact extendedPair_mem_tensorSuffixSupport S (phi.comp e.toLinearMap) t ht
  · refine iSup_le fun phi => ?_
    rintro x ⟨t, ht, rfl⟩
    have hu : e.rTensor Y t ∈ S.map (e.rTensor Y).toLinearMap := ⟨t, ht, rfl⟩
    have hc := extendedPair_mem_tensorSuffixSupport (S.map (e.rTensor Y).toLinearMap)
      (phi.comp e.symm.toLinearMap) _ hu
    have hphi : (phi.comp e.symm.toLinearMap).comp e.toLinearMap = phi := by
      ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [extendedPair_leftEquiv, hphi] at hc
    exact hc

/-- Specialize an arbitrary functional on the entire retained first two
factors after fixing the actual first-factor vector. -/
def specializeLeft (x : X) (eta : Module.Dual F (X ⊗[F] Y)) : Module.Dual F Y :=
  eta.comp (TensorProduct.mk F X Y x)

@[simp]
theorem specializeLeft_apply (x : X) (eta : Module.Dual F (X ⊗[F] Y)) (y : Y) :
    specializeLeft x eta y = eta (x ⊗ₜ[F] y) := rfl

/-- Prefix contraction through a fixed first factor retains that factor. -/
theorem contractRight_prepend (x : X) (t : Y ⊗[F] Z) (eta : Module.Dual F Z) :
    contractRight eta ((TensorProduct.assoc F X Y Z).symm (x ⊗ₜ[F] t)) =
      x ⊗ₜ[F] contractRight eta t := by
  have h := leftFlattening_prepend_apply (F := F) (Z := X) (X := Y) (Y := Z) x t eta
  simpa only [leftFlattening_apply] using h

/-- Whole-exterior suffix contraction specializes the whole functional
only after fixing the first actual tensor factor. -/
theorem extendedPair_prepend (x : X) (t : Y ⊗[F] Z)
    (eta : Module.Dual F (X ⊗[F] Y)) :
    extendedPair eta ((TensorProduct.assoc F X Y Z).symm (x ⊗ₜ[F] t)) =
      extendedPair (specializeLeft x eta) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
  | tmul y z =>
      simp only [TensorProduct.assoc_symm_tmul, extendedPair_tmul, specializeLeft_apply]

/-- Actual included product, with the cut retained inside its second block. -/
def tensorFrontProductSpace (S : Submodule F X) (T : Submodule F (Y ⊗[F] Z)) :
    Submodule F ((X ⊗[F] Y) ⊗[F] Z) :=
  (LinearMap.range (TensorProduct.map S.subtype T.subtype)).map
    (TensorProduct.assoc F X Y Z).symm.toLinearMap

/-- Every actual whole prefix contraction lies in S tensor the old prefix
support for arbitrary whole-exterior functionals. -/
theorem tensorFrontProductSpace_prefixSupport_le (S : Submodule F X)
    (T : Submodule F (Y ⊗[F] Z)) :
    tensorPrefixSupport (tensorFrontProductSpace S T) ≤
      LinearMap.range (TensorProduct.map S.subtype (tensorPrefixSupport T).subtype) := by
  refine iSup_le fun eta => ?_
  rintro x ⟨u, ⟨v, ⟨w, rfl⟩, rfl⟩, rfl⟩
  induction w using TensorProduct.induction_on with
  | zero =>
      change contractRight eta ((TensorProduct.assoc F X Y Z).symm.toLinearMap
        ((TensorProduct.map S.subtype T.subtype) 0)) ∈ _
      simp only [(TensorProduct.map S.subtype T.subtype).map_zero,
        (TensorProduct.assoc F X Y Z).symm.toLinearMap.map_zero, (contractRight eta).map_zero]
      exact Submodule.zero_mem _
  | add a b ha hb =>
      change contractRight eta ((TensorProduct.assoc F X Y Z).symm.toLinearMap
        ((TensorProduct.map S.subtype T.subtype) (a + b))) ∈ _
      simp only [(TensorProduct.map S.subtype T.subtype).map_add,
        (TensorProduct.assoc F X Y Z).symm.toLinearMap.map_add, (contractRight eta).map_add]
      exact Submodule.add_mem _ ha hb
  | tmul s t =>
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
      change contractRight eta ((TensorProduct.assoc F X Y Z).symm (s.val ⊗ₜ[F] t.val)) ∈ _
      rw [contractRight_prepend]
      let y : tensorPrefixSupport T := ⟨contractRight eta t.val,
        contractRight_mem_tensorPrefixSupport T eta t.val t.property⟩
      refine ⟨s ⊗ₜ[F] y, ?_⟩
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
      rfl

/-- Every arbitrary whole suffix functional specializes to an old second-
block functional, so suffix support does not grow. -/
theorem tensorFrontProductSpace_suffixSupport_le (S : Submodule F X)
    (T : Submodule F (Y ⊗[F] Z)) :
    tensorSuffixSupport (tensorFrontProductSpace S T) ≤ tensorSuffixSupport T := by
  refine iSup_le fun eta => ?_
  rintro x ⟨u, ⟨v, ⟨w, rfl⟩, rfl⟩, rfl⟩
  induction w using TensorProduct.induction_on with
  | zero =>
      change extendedPair eta ((TensorProduct.assoc F X Y Z).symm.toLinearMap
        ((TensorProduct.map S.subtype T.subtype) 0)) ∈ _
      simp only [(TensorProduct.map S.subtype T.subtype).map_zero,
        (TensorProduct.assoc F X Y Z).symm.toLinearMap.map_zero, (extendedPair eta).map_zero]
      exact Submodule.zero_mem _
  | add a b ha hb =>
      change extendedPair eta ((TensorProduct.assoc F X Y Z).symm.toLinearMap
        ((TensorProduct.map S.subtype T.subtype) (a + b))) ∈ _
      simp only [(TensorProduct.map S.subtype T.subtype).map_add,
        (TensorProduct.assoc F X Y Z).symm.toLinearMap.map_add, (extendedPair eta).map_add]
      exact Submodule.add_mem _ ha hb
  | tmul s t =>
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
      change extendedPair eta ((TensorProduct.assoc F X Y Z).symm (s.val ⊗ₜ[F] t.val)) ∈ _
      rw [extendedPair_prepend]
      exact extendedPair_mem_tensorSuffixSupport T (specializeLeft s.val eta) t.val t.property

theorem tensorFrontProductSpace_prefixSupport_finrank_le [FiniteDimensional F X]
    [FiniteDimensional F Y] (S : Submodule F X) (T : Submodule F (Y ⊗[F] Z)) :
    Module.finrank F (tensorPrefixSupport (tensorFrontProductSpace S T)) ≤
      Module.finrank F S * Module.finrank F (tensorPrefixSupport T) := by
  letI : FiniteDimensional F S := FiniteDimensional.of_injective S.subtype Subtype.val_injective
  letI : FiniteDimensional F (tensorPrefixSupport T) :=
    FiniteDimensional.of_injective (tensorPrefixSupport T).subtype Subtype.val_injective
  letI : Module.Free F S := Module.Free.of_basis (Module.Basis.ofVectorSpace F S)
  letI : Module.Free F (tensorPrefixSupport T) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace F (tensorPrefixSupport T))
  let f : S ⊗[F] (tensorPrefixSupport T) →ₗ[F] X ⊗[F] Y :=
    TensorProduct.map S.subtype (tensorPrefixSupport T).subtype
  letI : FiniteDimensional F (LinearMap.range f) :=
    FiniteDimensional.of_surjective f.rangeRestrict
      (LinearMap.range_eq_top.mp f.range_rangeRestrict)
  calc
    Module.finrank F (tensorPrefixSupport (tensorFrontProductSpace S T)) ≤
        Module.finrank F (LinearMap.range f) :=
      Submodule.finrank_mono (tensorFrontProductSpace_prefixSupport_le S T)
    _ ≤ Module.finrank F (S ⊗[F] (tensorPrefixSupport T)) := LinearMap.finrank_range_le f
    _ = Module.finrank F S * Module.finrank F (tensorPrefixSupport T) := Module.finrank_tensorProduct

theorem tensorFrontProductSpace_suffixSupport_finrank_le [FiniteDimensional F Z]
    (S : Submodule F X) (T : Submodule F (Y ⊗[F] Z)) :
    Module.finrank F (tensorSuffixSupport (tensorFrontProductSpace S T)) ≤
      Module.finrank F (tensorSuffixSupport T) :=
  Submodule.finrank_mono (tensorFrontProductSpace_suffixSupport_le S T)

/-- Retained-factor transport in the form used by the word-cut bridge. -/
theorem tensorFrontProductSpace_leftEquiv_prefixSupport_finrank_le
    [FiniteDimensional F X] [FiniteDimensional F Y] (e : X ⊗[F] Y ≃ₗ[F] A)
    (S : Submodule F X) (T : Submodule F (Y ⊗[F] Z)) :
    Module.finrank F (tensorPrefixSupport
      ((tensorFrontProductSpace S T).map (e.rTensor Z).toLinearMap)) ≤
      Module.finrank F S * Module.finrank F (tensorPrefixSupport T) := by
  rw [tensorPrefixSupport_leftEquiv, e.finrank_map_eq]
  exact tensorFrontProductSpace_prefixSupport_finrank_le S T

theorem tensorFrontProductSpace_leftEquiv_suffixSupport_finrank_le
    [FiniteDimensional F Z] (e : X ⊗[F] Y ≃ₗ[F] A)
    (S : Submodule F X) (T : Submodule F (Y ⊗[F] Z)) :
    Module.finrank F (tensorSuffixSupport
      ((tensorFrontProductSpace S T).map (e.rTensor Z).toLinearMap)) ≤
      Module.finrank F (tensorSuffixSupport T) := by
  rw [tensorSuffixSupport_leftEquiv]
  exact tensorFrontProductSpace_suffixSupport_finrank_le S T

#print axioms CriticalGK2.ContractionBudget.tensorFrontProductSpace_prefixSupport_le
#print axioms CriticalGK2.ContractionBudget.tensorFrontProductSpace_suffixSupport_le
#print axioms CriticalGK2.ContractionBudget.tensorFrontProductSpace_prefixSupport_finrank_le
#print axioms CriticalGK2.ContractionBudget.tensorFrontProductSpace_suffixSupport_finrank_le
#print axioms CriticalGK2.ContractionBudget.tensorPrefixSupport_leftEquiv
#print axioms CriticalGK2.ContractionBudget.tensorSuffixSupport_leftEquiv

end

end CriticalGK2.ContractionBudget
