import CriticalGK2.FreeTailCutSupport
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Honest support bounds for an entire tensor product of block spaces

At a cut inside the first block, arbitrary whole-outside contractions leave
prefix support inside the original prefix support. The suffix support lies
in the actual included tensor product of the old suffix support and the
whole second block. This is the multiplicative budget mechanism used for
block powers.
-/

namespace CriticalGK2.ContractionBudget

noncomputable section

open TensorProduct

variable {F X Y Z : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]
  [AddCommGroup Z] [Module F Z]

theorem tensorPrefixSupport_mono {S T : Submodule F (X ⊗[F] Y)} (h : S ≤ T) :
    tensorPrefixSupport S ≤ tensorPrefixSupport T :=
  iSup_le fun eta => (Submodule.map_mono h).trans
    (le_iSup (fun theta : Module.Dual F Y => T.map (contractRight theta)) eta)

theorem tensorSuffixSupport_mono {S T : Submodule F (X ⊗[F] Y)} (h : S ≤ T) :
    tensorSuffixSupport S ≤ tensorSuffixSupport T :=
  iSup_le fun phi => (Submodule.map_mono h).trans
    (le_iSup (fun psi : Module.Dual F X => T.map (extendedPair psi)) phi)

/-- Actual included tensor product, retaining the first-block cut. -/
def tensorTailProductSpace (S : Submodule F (X ⊗[F] Y)) (T : Submodule F Z) :
    Submodule F (X ⊗[F] (Y ⊗[F] Z)) :=
  (LinearMap.range (TensorProduct.map S.subtype T.subtype)).map
    (TensorProduct.assoc F X Y Z).toLinearMap

theorem tensorTailProductSpace_prefixSupport_le (S : Submodule F (X ⊗[F] Y))
    (T : Submodule F Z) :
    tensorPrefixSupport (tensorTailProductSpace S T) ≤ tensorPrefixSupport S := by
  refine iSup_le fun eta => ?_
  rintro x ⟨u, ⟨v, ⟨w, rfl⟩, rfl⟩, rfl⟩
  induction w using TensorProduct.induction_on with
  | zero =>
      change contractRight eta ((TensorProduct.assoc F X Y Z).toLinearMap
        ((TensorProduct.map S.subtype T.subtype) 0)) ∈ _
      simp only [(TensorProduct.map S.subtype T.subtype).map_zero,
        (TensorProduct.assoc F X Y Z).toLinearMap.map_zero, (contractRight eta).map_zero]
      exact Submodule.zero_mem _
  | add a b ha hb =>
      change contractRight eta ((TensorProduct.assoc F X Y Z).toLinearMap
        ((TensorProduct.map S.subtype T.subtype) (a + b))) ∈ _
      simp only [(TensorProduct.map S.subtype T.subtype).map_add,
        (TensorProduct.assoc F X Y Z).toLinearMap.map_add, (contractRight eta).map_add]
      exact Submodule.add_mem _ ha hb
  | tmul s t =>
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
      change contractRight eta ((TensorProduct.assoc F X Y Z) (s.val ⊗ₜ[F] t.val)) ∈ _
      have he := leftFlattening_append_apply (F := F) (X := X) (Y := Y) (Z := Z)
        s.val t.val eta
      simp only [leftFlattening_apply] at he
      rw [he]
      exact contractRight_mem_tensorPrefixSupport S (specializeRight t.val eta) s.val s.property

theorem tensorTailProductSpace_suffixSupport_le (S : Submodule F (X ⊗[F] Y))
    (T : Submodule F Z) :
    tensorSuffixSupport (tensorTailProductSpace S T) ≤
      LinearMap.range (TensorProduct.map (tensorSuffixSupport S).subtype T.subtype) := by
  refine iSup_le fun phi => ?_
  rintro x ⟨u, ⟨v, ⟨w, rfl⟩, rfl⟩, rfl⟩
  induction w using TensorProduct.induction_on with
  | zero =>
      change extendedPair phi ((TensorProduct.assoc F X Y Z).toLinearMap
        ((TensorProduct.map S.subtype T.subtype) 0)) ∈ _
      simp only [(TensorProduct.map S.subtype T.subtype).map_zero,
        (TensorProduct.assoc F X Y Z).toLinearMap.map_zero, (extendedPair phi).map_zero]
      exact Submodule.zero_mem _
  | add a b ha hb =>
      change extendedPair phi ((TensorProduct.assoc F X Y Z).toLinearMap
        ((TensorProduct.map S.subtype T.subtype) (a + b))) ∈ _
      simp only [(TensorProduct.map S.subtype T.subtype).map_add,
        (TensorProduct.assoc F X Y Z).toLinearMap.map_add, (extendedPair phi).map_add]
      exact Submodule.add_mem _ ha hb
  | tmul s t =>
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
      change extendedPair phi ((TensorProduct.assoc F X Y Z) (s.val ⊗ₜ[F] t.val)) ∈ _
      rw [extendedPair_append (F := F) (X := X) (Y := Y) (Z := Z) phi s.val t.val]
      let y : tensorSuffixSupport S := ⟨extendedPair phi s.val,
        extendedPair_mem_tensorSuffixSupport S phi s.val s.property⟩
      refine ⟨y ⊗ₜ[F] t, ?_⟩
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
      rfl

theorem tensorTailProductSpace_prefixSupport_finrank_le [FiniteDimensional F X]
    (S : Submodule F (X ⊗[F] Y)) (T : Submodule F Z) :
    Module.finrank F (tensorPrefixSupport (tensorTailProductSpace S T)) ≤
      Module.finrank F (tensorPrefixSupport S) :=
  Submodule.finrank_mono (tensorTailProductSpace_prefixSupport_le S T)

theorem tensorTailProductSpace_suffixSupport_finrank_le [FiniteDimensional F Y]
    [FiniteDimensional F Z] (S : Submodule F (X ⊗[F] Y)) (T : Submodule F Z) :
    Module.finrank F (tensorSuffixSupport (tensorTailProductSpace S T)) ≤
      Module.finrank F (tensorSuffixSupport S) * Module.finrank F T := by
  letI : Module.Free F (tensorSuffixSupport S) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace F (tensorSuffixSupport S))
  letI : Module.Free F T := Module.Free.of_basis (Module.Basis.ofVectorSpace F T)
  let f : (tensorSuffixSupport S) ⊗[F] T →ₗ[F] Y ⊗[F] Z :=
    TensorProduct.map (tensorSuffixSupport S).subtype T.subtype
  letI : FiniteDimensional F (LinearMap.range f) :=
    FiniteDimensional.of_surjective f.rangeRestrict
      (LinearMap.range_eq_top.mp f.range_rangeRestrict)
  calc
    Module.finrank F (tensorSuffixSupport (tensorTailProductSpace S T)) ≤
        Module.finrank F (LinearMap.range f) :=
      Submodule.finrank_mono (tensorTailProductSpace_suffixSupport_le S T)
    _ ≤ Module.finrank F ((tensorSuffixSupport S) ⊗[F] T) := LinearMap.finrank_range_le f
    _ = Module.finrank F (tensorSuffixSupport S) * Module.finrank F T := Module.finrank_tensorProduct

#print axioms CriticalGK2.ContractionBudget.tensorTailProductSpace_prefixSupport_le
#print axioms CriticalGK2.ContractionBudget.tensorTailProductSpace_suffixSupport_finrank_le

end

end CriticalGK2.ContractionBudget
