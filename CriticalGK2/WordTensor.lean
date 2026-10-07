import CriticalGK2.ActualWordSpaces
import CriticalGK2.LongCut
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Actual homogeneous word tensor products

The concatenation equivalences in this file use the actual degree components
of `MonoidAlgebra F (FreeMonoid Bool)`, with their actual word bases.  The
tensor equivalence is proved to be the actual multiplication map.  Its dual
equivalence preserves the product pairing.

The final prefix contraction theorem transports `LongCut` through these
proved word-space equivalences.  It states preservation of a specified
complete block in actual homogeneous dual spaces.
-/

namespace CriticalGK2.Actual

open TensorProduct

variable (F : Type*) [Field F]

/-- The actual monomial basis of the actual homogeneous component. -/
noncomputable def homogeneousWordBasis (n : ℕ) :
    Module.Basis (LengthWord n) F (homogeneous F n) :=
  Finsupp.basisSingleOne.map (homogeneousWordEquiv F n).symm

@[simp]
theorem homogeneousWordBasis_coe (n : ℕ) (w : LengthWord n) :
    ((homogeneousWordBasis F n w) : WordAlgebra F) = MonoidAlgebra.single w.val 1 := by
  simp only [homogeneousWordBasis, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  change ((Finsupp.supportedEquivFinsupp (R := F) (wordsOfLength n)).symm
    (Finsupp.single w (1 : F))).val = _
  exact Finsupp.supportedEquivFinsupp_symm_single (R := F) (wordsOfLength n) w (1 : F)

noncomputable instance homogeneousFiniteDimensional (n : ℕ) :
    FiniteDimensional F (homogeneous F n) :=
  Module.Basis.finiteDimensional_of_finite (homogeneousWordBasis F n)

/-- Actual concatenation of homogeneous components, specified on actual
word basis vectors by concatenation of actual words. -/
noncomputable def homogeneousTensorConcat (a b : ℕ) :
    (homogeneous F a) ⊗[F] (homogeneous F b) ≃ₗ[F] homogeneous F (a + b) :=
  (Module.Basis.tensorProduct (homogeneousWordBasis F a) (homogeneousWordBasis F b)).equiv
    (homogeneousWordBasis F (a + b)) (concatenateEquiv a b)

@[simp]
theorem homogeneousTensorConcat_basis (a b : ℕ)
    (u : LengthWord a) (v : LengthWord b) :
    homogeneousTensorConcat F a b
      (homogeneousWordBasis F a u ⊗ₜ[F] homogeneousWordBasis F b v) =
      homogeneousWordBasis F (a + b) (concatenate u v) := by
  simpa only [homogeneousTensorConcat, Module.Basis.tensorProduct_apply,
    concatenateEquiv_apply] using
    (Module.Basis.equiv_apply
      (Module.Basis.tensorProduct (homogeneousWordBasis F a) (homogeneousWordBasis F b))
      (u, v) (homogeneousWordBasis F (a + b)) (concatenateEquiv a b))

/-- Actual ambient multiplication, restricted to its homogeneous degrees. -/
noncomputable def homogeneousMultiplication (a b : ℕ) :
    homogeneous F a →ₗ[F] homogeneous F b →ₗ[F] homogeneous F (a + b) where
  toFun x :=
    { toFun := fun y => ⟨x.val * y.val, homogeneous_mul F x.property y.property⟩
      map_add' := by
        intro y y'
        apply Subtype.ext
        exact mul_add x.val y.val y'.val
      map_smul' := by
        intro c y
        apply Subtype.ext
        exact mul_smul_comm c x.val y.val }
  map_add' := by
    intro x x'
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact add_mul x.val x'.val y.val
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact smul_mul_assoc c x.val y.val

/-- The word-basis tensor equivalence is the actual multiplication map. -/
theorem homogeneousTensorConcat_toLinearMap (a b : ℕ) :
    (homogeneousTensorConcat F a b).toLinearMap =
      TensorProduct.lift (homogeneousMultiplication F a b) := by
  apply (Module.Basis.tensorProduct (homogeneousWordBasis F a)
    (homogeneousWordBasis F b)).ext
  rintro ⟨u, v⟩
  simp only [Module.Basis.tensorProduct_apply, LinearEquiv.coe_coe,
    homogeneousTensorConcat_basis, TensorProduct.lift.tmul]
  apply Subtype.ext
  simp [homogeneousMultiplication, homogeneousWordBasis_coe,
    MonoidAlgebra.single_mul_single, concatenate_val]

@[simp]
theorem homogeneousTensorConcat_tmul (a b : ℕ)
    (x : homogeneous F a) (y : homogeneous F b) :
    homogeneousTensorConcat F a b (x ⊗ₜ[F] y) =
      homogeneousMultiplication F a b x y := by
  exact LinearMap.congr_fun (homogeneousTensorConcat_toLinearMap F a b) (x ⊗ₜ[F] y)

@[simp]
theorem homogeneousTensorConcat_tmul_coe (a b : ℕ)
    (x : homogeneous F a) (y : homogeneous F b) :
    (homogeneousTensorConcat F a b (x ⊗ₜ[F] y) : WordAlgebra F) = x.val * y.val := by
  rw [homogeneousTensorConcat_tmul]
  rfl

/-- Actual dual concatenation, constructed from proved homogeneous
multiplication and the finite free tensor-dual equivalence. -/
noncomputable def homogeneousDualTensorConcat (a b : ℕ) :
    (HomogeneousDual F a) ⊗[F] (HomogeneousDual F b) ≃ₗ[F]
      HomogeneousDual F (a + b) := by
  classical
  exact (TensorProduct.dualDistribEquivOfBasis
      (homogeneousWordBasis F a) (homogeneousWordBasis F b)).trans
      (homogeneousTensorConcat F a b).symm.dualMap

/-- The dual concatenation has exactly the actual product pairing. -/
@[simp]
theorem homogeneousDualTensorConcat_pairing (a b : ℕ)
    (φ : HomogeneousDual F a) (ψ : HomogeneousDual F b)
    (x : homogeneous F a) (y : homogeneous F b) :
    homogeneousDualTensorConcat F a b (φ ⊗ₜ[F] ψ)
      (homogeneousTensorConcat F a b (x ⊗ₜ[F] y)) = φ x * ψ y := by
  classical
  change TensorProduct.dualDistrib F (homogeneous F a) (homogeneous F b)
    (φ ⊗ₜ[F] ψ)
    ((homogeneousTensorConcat F a b).symm
      (homogeneousTensorConcat F a b (x ⊗ₜ[F] y))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.dualDistrib_apply]

/-- Three actual dual word factors with a fixed association convention. -/
noncomputable def homogeneousDualTripleConcat (a b c : ℕ) :
    HomogeneousDual F a ⊗[F] (HomogeneousDual F b ⊗[F] HomogeneousDual F c) ≃ₗ[F]
      HomogeneousDual F (a + (b + c)) :=
  (homogeneousDualTensorConcat F b c).lTensor (HomogeneousDual F a) ≪≫ₗ
    homogeneousDualTensorConcat F a (b + c)

/-- Actual prefix contraction of an actual homogeneous dual element.  The
functional contracts the entire degree-c external dual space. -/
noncomputable def actualPrefixContraction (a b c : ℕ)
    (φ : Module.Dual F (HomogeneousDual F c)) :
    HomogeneousDual F (a + (b + c)) →ₗ[F] HomogeneousDual F (a + b) :=
  (homogeneousDualTensorConcat F a b).toLinearMap.comp
    ((CriticalGK2.contractLast φ).comp
      (homogeneousDualTripleConcat F a b c).symm.toLinearMap)

/-- Actual ambient dual space whose complete degree-a left block belongs
to W, before the external contraction. -/
noncomputable def actualLeftBlockTripleSpace (a b c : ℕ)
    (W : Submodule F (HomogeneousDual F a)) :
    Submodule F (HomogeneousDual F (a + (b + c))) :=
  (LinearMap.range (W.subtype.rTensor (HomogeneousDual F b ⊗[F] HomogeneousDual F c))).map
    (homogeneousDualTripleConcat F a b c).toLinearMap

/-- Actual retained degree-(a+b) dual space with its complete W block. -/
noncomputable def actualLeftBlockSpace (a b : ℕ)
    (W : Submodule F (HomogeneousDual F a)) :
    Submodule F (HomogeneousDual F (a + b)) :=
  (LinearMap.range (W.subtype.rTensor (HomogeneousDual F b))).map
    (homogeneousDualTensorConcat F a b).toLinearMap

/-- Arbitrary whole-external-space contraction preserves the complete W
block in the actual homogeneous dual spaces. -/
theorem actualPrefixContraction_mem (a b c : ℕ)
    (W : Submodule F (HomogeneousDual F a))
    (φ : Module.Dual F (HomogeneousDual F c))
    (z : HomogeneousDual F (a + (b + c)))
    (hz : z ∈ actualLeftBlockTripleSpace F a b c W) :
    actualPrefixContraction F a b c φ z ∈ actualLeftBlockSpace F a b W := by
  obtain ⟨w, hw, rfl⟩ := hz
  change homogeneousDualTensorConcat F a b
    (CriticalGK2.contractLast φ
      ((homogeneousDualTripleConcat F a b c).symm
        (homogeneousDualTripleConcat F a b c w))) ∈ _
  rw [LinearEquiv.symm_apply_apply]
  exact ⟨CriticalGK2.contractLast φ w,
    CriticalGK2.contractLast_mem_left_support W φ w hw, rfl⟩

end CriticalGK2.Actual
