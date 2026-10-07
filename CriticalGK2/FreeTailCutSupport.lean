import CriticalGK2.TensorCutRank

/-!
# Full cut support of a fixed stem with a free last factor

The subspace is the actual range of `z ↦ assoc(t ⊗ z)`. Every support below
is a supremum over all whole-exterior functionals. The prefix support equals
the honest prefix flattening range of t; the suffix support is exactly the
actual scalar extension of its suffix flattening range. Hence its dimensions
are r and r*dim(Z), derived from actual spaces and actual maps.
-/

namespace CriticalGK2.ContractionBudget

noncomputable section

open TensorProduct

variable {F X Y Z : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]
  [AddCommGroup Z] [Module F Z]

def tensorPrefixSupport (S : Submodule F (X ⊗[F] Y)) : Submodule F X :=
  ⨆ eta : Module.Dual F Y, S.map (contractRight eta)

def tensorSuffixSupport (S : Submodule F (X ⊗[F] Y)) : Submodule F Y :=
  ⨆ phi : Module.Dual F X, S.map (extendedPair phi)

/-- Actual free tail after a fixed, arbitrary tensor stem. -/
def freeTailTensorSpace (t : X ⊗[F] Y) : Submodule F (X ⊗[F] (Y ⊗[F] Z)) :=
  LinearMap.range ((TensorProduct.assoc F X Y Z).toLinearMap.comp
    (TensorProduct.mk F (X ⊗[F] Y) Z t))

theorem contractRight_mem_tensorPrefixSupport (S : Submodule F (X ⊗[F] Y))
    (eta : Module.Dual F Y) (u : X ⊗[F] Y) (hu : u ∈ S) :
    contractRight eta u ∈ tensorPrefixSupport S :=
  (le_iSup (fun theta : Module.Dual F Y => S.map (contractRight theta)) eta)
    ⟨u, hu, rfl⟩

theorem extendedPair_mem_tensorSuffixSupport (S : Submodule F (X ⊗[F] Y))
    (phi : Module.Dual F X) (u : X ⊗[F] Y) (hu : u ∈ S) :
    extendedPair phi u ∈ tensorSuffixSupport S :=
  (le_iSup (fun psi : Module.Dual F X => S.map (extendedPair psi)) phi)
    ⟨u, hu, rfl⟩

/-- Actual whole-exterior suffix contraction through an appended factor. -/
theorem extendedPair_append (phi : Module.Dual F X) (t : X ⊗[F] Y) (z : Z) :
    extendedPair phi (TensorProduct.assoc F X Y Z (t ⊗ₜ[F] z)) =
      extendedPair phi t ⊗ₜ[F] z := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [add_tmul, map_add, ha, hb]
  | tmul x y => simp only [TensorProduct.assoc_tmul, extendedPair_tmul, smul_tmul']

/-- No whole-exterior prefix functional adds support after a free tail,
and a fixed nonzero tail recovers every old prefix functional. -/
theorem freeTailTensorSpace_prefixSupport (t : X ⊗[F] Y) (z0 : Z) (hz0 : z0 ≠ 0) :
    tensorPrefixSupport (freeTailTensorSpace (Z := Z) t) =
      LinearMap.range (leftFlattening t) := by
  apply le_antisymm
  · refine iSup_le fun eta => ?_
    rintro x ⟨u, hu, rfl⟩
    obtain ⟨z, rfl⟩ := hu
    exact ⟨specializeRight z eta, (leftFlattening_append_apply t z eta).symm⟩
  · rintro x ⟨eta, rfl⟩
    obtain ⟨theta, htheta⟩ := specializeRight_surjective z0 hz0 eta
    have hm : TensorProduct.assoc F X Y Z (t ⊗ₜ[F] z0) ∈
        freeTailTensorSpace (Z := Z) t := ⟨z0, rfl⟩
    have hc := contractRight_mem_tensorPrefixSupport
      (freeTailTensorSpace (Z := Z) t) theta _ hm
    have he : contractRight theta (TensorProduct.assoc F X Y Z (t ⊗ₜ[F] z0)) =
        leftFlattening t eta := by
      rw [← leftFlattening_apply, leftFlattening_append_apply, htheta]
    rw [he] at hc
    exact hc

/-- The entire actual suffix support is the included tensor product of the
old suffix support with the free final factor. -/
theorem freeTailTensorSpace_suffixSupport (t : X ⊗[F] Y) :
    tensorSuffixSupport (freeTailTensorSpace (Z := Z) t) =
      scalarExtension (C := Z) (LinearMap.range (rightFlattening t)) := by
  apply le_antisymm
  · refine iSup_le fun phi => ?_
    rintro x ⟨u, hu, rfl⟩
    obtain ⟨z, rfl⟩ := hu
    let y : LinearMap.range (rightFlattening t) := ⟨rightFlattening t phi, ⟨phi, rfl⟩⟩
    refine ⟨y ⊗ₜ[F] z, ?_⟩
    simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.mk_apply,
      extendedPair_append, rightFlattening_apply]
    rfl
  · intro x hx
    obtain ⟨u, rfl⟩ := hx
    induction u using TensorProduct.induction_on with
    | zero =>
        rw [(LinearMap.range (rightFlattening t)).subtype.rTensor Z |>.map_zero]
        exact Submodule.zero_mem _
    | add a b ha hb =>
        rw [map_add]
        exact Submodule.add_mem _ ha hb
    | tmul y z =>
        obtain ⟨phi, hphi⟩ := y.property
        have hm : TensorProduct.assoc F X Y Z (t ⊗ₜ[F] z) ∈
            freeTailTensorSpace (Z := Z) t := ⟨z, rfl⟩
        have hc := extendedPair_mem_tensorSuffixSupport
          (freeTailTensorSpace (Z := Z) t) phi _ hm
        rw [extendedPair_append, ← rightFlattening_apply, hphi] at hc
        simpa only [LinearMap.rTensor_tmul, Submodule.subtype_apply] using hc

/-- The actual included tensor image has its actual full tensor dimension.
Injectivity is proved by tensoring an actual linear left inverse. -/
theorem scalarExtension_finrank {A B : Type*} [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B] [FiniteDimensional F A] [FiniteDimensional F B]
    (S : Submodule F A) :
    Module.finrank F (scalarExtension (C := B) S) =
      Module.finrank F S * Module.finrank F B := by
  letI : FiniteDimensional F S := FiniteDimensional.of_injective S.subtype Subtype.val_injective
  letI : Module.Free F S := Module.Free.of_basis (Module.Basis.ofVectorSpace F S)
  letI : Module.Free F B := Module.Free.of_basis (Module.Basis.ofVectorSpace F B)
  obtain ⟨g, hg⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  have hleft : (g.rTensor B).comp (S.subtype.rTensor B) = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, hg, LinearMap.rTensor_id]
  have hinj : Function.Injective (S.subtype.rTensor B) := by
    intro a b hab
    calc
      a = (g.rTensor B) ((S.subtype.rTensor B) a) := (LinearMap.congr_fun hleft a).symm
      _ = (g.rTensor B) ((S.subtype.rTensor B) b) := congrArg (g.rTensor B) hab
      _ = b := LinearMap.congr_fun hleft b
  change Module.finrank F (LinearMap.range (S.subtype.rTensor B)) = _
  rw [LinearMap.finrank_range_of_inj hinj]
  exact Module.finrank_tensorProduct

theorem freeTailTensorSpace_prefixSupport_finrank (t : X ⊗[F] Y)
    (z0 : Z) (hz0 : z0 ≠ 0) :
    Module.finrank F (tensorPrefixSupport (freeTailTensorSpace (Z := Z) t)) =
      tensorCutRank t := by
  rw [freeTailTensorSpace_prefixSupport t z0 hz0]
  rfl

theorem freeTailTensorSpace_suffixSupport_finrank [FiniteDimensional F X]
    [FiniteDimensional F Y] [FiniteDimensional F Z] (t : X ⊗[F] Y) :
    Module.finrank F (tensorSuffixSupport (freeTailTensorSpace (Z := Z) t)) =
      tensorCutRank t * Module.finrank F Z := by
  rw [freeTailTensorSpace_suffixSupport, scalarExtension_finrank,
    rightFlattening_finrank_eq_left]

#print axioms CriticalGK2.ContractionBudget.freeTailTensorSpace_prefixSupport
#print axioms CriticalGK2.ContractionBudget.freeTailTensorSpace_suffixSupport_finrank

end

end CriticalGK2.ContractionBudget
