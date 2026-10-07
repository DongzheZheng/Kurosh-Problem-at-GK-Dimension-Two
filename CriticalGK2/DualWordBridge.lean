import CriticalGK2.StemPolynomial
import CriticalGK2.WordCoherence
import CriticalGK2.HomogeneousProjection

/-!
# Actual word-coefficient identification with homogeneous duals

The identification is the linear equivalence from the actual word basis to its
actual dual basis. Multiplication compatibility is proved on the tensor
word basis and then evaluated on every word.
-/

namespace CriticalGK2.Actual

noncomputable section

local instance (n : ℕ) : DecidableEq (LengthWord n) := Classical.decEq _

open TensorProduct

variable (F : Type*) [Field F]

/-- The coefficient condition used by the PI modules is the actual homogeneous
supported-submodule membership condition. -/
theorem wordHomogeneous_iff_mem_homogeneous (n : ℕ) (P : WordAlgebra F) :
    CriticalGK2.WordHomogeneous n P ↔ P ∈ homogeneous F n := by
  rw [mem_homogeneous_iff]
  constructor
  · intro h w hw
    by_contra hne
    exact hw (h w hne)
  · intro h w hw
    by_contra hlen
    exact hw (h w hlen)

/-- The actual word basis identifies a homogeneous polynomial with the
functional having exactly the same word coefficients. -/
noncomputable def coefficientSelfDual (n : ℕ) :
    homogeneous F n ≃ₗ[F] HomogeneousDual F n :=
  (homogeneousWordBasis F n).equiv (homogeneousWordBasis F n).dualBasis
    (Equiv.refl (LengthWord n))

@[simp]
theorem coefficientSelfDual_basis (n : ℕ) (w : LengthWord n) :
    coefficientSelfDual F n (homogeneousWordBasis F n w) =
      (homogeneousWordBasis F n).dualBasis w := by
  change (homogeneousWordBasis F n).equiv (homogeneousWordBasis F n).dualBasis
    (Equiv.refl (LengthWord n)) (homogeneousWordBasis F n w) = _
  exact (homogeneousWordBasis F n).equiv_apply w
    (homogeneousWordBasis F n).dualBasis (Equiv.refl (LengthWord n))

/-- Actual evaluation at an actual word basis vector. -/
def dualWordCoefficient (n : ℕ) (w : LengthWord n) : HomogeneousDual F n →ₗ[F] F where
  toFun φ := φ (homogeneousWordBasis F n w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual ambient coefficient, restricted to one homogeneous degree. -/
def homogeneousWordCoefficient (n : ℕ) (w : LengthWord n) : homogeneous F n →ₗ[F] F where
  toFun P := P.val w.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The basis-to-dual-basis equivalence reads back the original word coefficients. -/
theorem coefficientSelfDual_word_coefficient (n : ℕ)
    (P : homogeneous F n) (w : LengthWord n) :
    coefficientSelfDual F n P (homogeneousWordBasis F n w) = P.val w.val := by
  classical
  have heq : (dualWordCoefficient F n w).comp (coefficientSelfDual F n).toLinearMap =
      homogeneousWordCoefficient F n w := by
    apply (homogeneousWordBasis F n).ext
    intro v
    change coefficientSelfDual F n (homogeneousWordBasis F n v)
      (homogeneousWordBasis F n w) = (homogeneousWordBasis F n v).val w.val
    rw [coefficientSelfDual_basis, homogeneousWordBasis_coe]
    change ((homogeneousWordBasis F n).dualBasis v) (homogeneousWordBasis F n w) =
      (Finsupp.single v.val (1 : F)) w.val
    simp [Module.Basis.coe_dualBasis, Module.Basis.coord_apply,
      Finsupp.single_apply, Subtype.val_inj, eq_comm]
  exact LinearMap.congr_fun heq P

/-- Concatenation equality is exact equality of its two cut words. -/
theorem concatenate_eq_iff {a b : ℕ} (u u' : LengthWord a) (v v' : LengthWord b) :
    concatenate u v = concatenate u' v' ↔ u = u' ∧ v = v' := by
  change (concatenateEquiv a b) (u, v) = (concatenateEquiv a b) (u', v') ↔ _
  rw [(concatenateEquiv a b).injective.eq_iff, Prod.mk.injEq]

/-- The coefficient identification commutes with actual tensor concatenation. -/
theorem coefficientSelfDual_tensorConcat (a b : ℕ) :
    (coefficientSelfDual F (a + b)).toLinearMap.comp
        (homogeneousTensorConcat F a b).toLinearMap =
      (homogeneousDualTensorConcat F a b).toLinearMap.comp
        (TensorProduct.map (coefficientSelfDual F a).toLinearMap
          (coefficientSelfDual F b).toLinearMap) := by
  apply (Module.Basis.tensorProduct (homogeneousWordBasis F a)
    (homogeneousWordBasis F b)).ext
  rintro ⟨u, v⟩
  simp only [Module.Basis.tensorProduct_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    homogeneousTensorConcat_basis, TensorProduct.map_tmul, coefficientSelfDual_basis]
  apply (homogeneousWordBasis F (a + b)).ext
  intro w
  obtain ⟨⟨u', v'⟩, rfl⟩ := (concatenateEquiv a b).surjective w
  change ((homogeneousWordBasis F (a + b)).dualBasis (concatenate u v))
      (homogeneousWordBasis F (a + b) (concatenate u' v')) =
    homogeneousDualTensorConcat F a b
      ((homogeneousWordBasis F a).dualBasis u ⊗ₜ[F] (homogeneousWordBasis F b).dualBasis v)
      (homogeneousWordBasis F (a + b) (concatenate u' v'))
  have hr := homogeneousDualTensorConcat_pairing F a b
    ((homogeneousWordBasis F a).dualBasis u) ((homogeneousWordBasis F b).dualBasis v)
    (homogeneousWordBasis F a u') (homogeneousWordBasis F b v')
  rw [homogeneousTensorConcat_basis] at hr
  rw [hr]
  by_cases hu : u = u' <;> by_cases hv : v = v' <;>
    simp [Module.Basis.coe_dualBasis, Module.Basis.coord_apply,
      Module.Basis.repr_self_apply, concatenate_eq_iff, hu, hv]

/-- Actual polynomial multiplication corresponds to actual dual tensor multiplication. -/
theorem coefficientSelfDual_mul (a b : ℕ)
    (P : homogeneous F a) (Q : homogeneous F b) :
    coefficientSelfDual F (a + b) (homogeneousMultiplication F a b P Q) =
      homogeneousDualTensorConcat F a b
        (coefficientSelfDual F a P ⊗ₜ[F] coefficientSelfDual F b Q) := by
  have h := LinearMap.congr_fun (coefficientSelfDual_tensorConcat F a b) (P ⊗ₜ[F] Q)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, homogeneousTensorConcat_tmul,
    TensorProduct.map_tmul] using h

/-- Extend the coefficient identification to ambient polynomials using the
proved actual homogeneous projection. -/
noncomputable def ambientToDual (n : ℕ) : WordAlgebra F →ₗ[F] HomogeneousDual F n :=
  (coefficientSelfDual F n).toLinearMap.comp (homogeneousProjection F n)

/-- The inverse coefficient identification included into the actual ambient algebra. -/
noncomputable def dualToAmbient (n : ℕ) : HomogeneousDual F n →ₗ[F] WordAlgebra F :=
  (homogeneous F n).subtype.comp (coefficientSelfDual F n).symm.toLinearMap

@[simp]
theorem dualToAmbient_ambientToDual (n : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F n) :
    dualToAmbient F n (ambientToDual F n P) = P := by
  simp only [dualToAmbient, ambientToDual, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact homogeneousProjection_of_mem F n P hP

@[simp]
theorem ambientToDual_dualToAmbient (n : ℕ) (φ : HomogeneousDual F n) :
    ambientToDual F n (dualToAmbient F n φ) = φ := by
  have hp : homogeneousProjection F n ((coefficientSelfDual F n).symm φ).val =
      (coefficientSelfDual F n).symm φ := by
    apply Subtype.ext
    exact homogeneousProjection_of_mem F n _ ((coefficientSelfDual F n).symm φ).property
  simp only [ambientToDual, dualToAmbient, LinearMap.comp_apply]
  change coefficientSelfDual F n
    (homogeneousProjection F n ((coefficientSelfDual F n).symm φ).val) = φ
  rw [hp, LinearEquiv.apply_symm_apply]

/-- Nonzero homogeneous polynomials remain nonzero actual dual elements. -/
theorem ambientToDual_ne_zero (n : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F n) (hne : P ≠ 0) : ambientToDual F n P ≠ 0 := by
  intro h
  apply hne
  rw [← dualToAmbient_ambientToDual F n P hP, h, map_zero]

/-- Ambient multiplication of homogeneous polynomials becomes actual dual concatenation. -/
theorem ambientToDual_mul (a b : ℕ) (P Q : WordAlgebra F)
    (hP : P ∈ homogeneous F a) (hQ : Q ∈ homogeneous F b) :
    ambientToDual F (a + b) (P * Q) =
      homogeneousDualTensorConcat F a b (ambientToDual F a P ⊗ₜ[F] ambientToDual F b Q) := by
  have hp : homogeneousProjection F a P = ⟨P, hP⟩ := by
    apply Subtype.ext
    exact homogeneousProjection_of_mem F a P hP
  have hq : homogeneousProjection F b Q = ⟨Q, hQ⟩ := by
    apply Subtype.ext
    exact homogeneousProjection_of_mem F b Q hQ
  have hpq : homogeneousProjection F (a + b) (P * Q) =
      homogeneousMultiplication F a b ⟨P, hP⟩ ⟨Q, hQ⟩ := by
    apply Subtype.ext
    exact homogeneousProjection_of_mem F (a + b) _ (homogeneous_mul F hP hQ)
  simp only [ambientToDual, LinearMap.comp_apply]
  rw [hp, hq, hpq]
  exact coefficientSelfDual_mul F a b ⟨P, hP⟩ ⟨Q, hQ⟩

/-- Conversely, the actual dual concatenation reconstructs the actual polynomial product. -/
theorem dualToAmbient_tensorConcat (a b : ℕ)
    (φ : HomogeneousDual F a) (ψ : HomogeneousDual F b) :
    dualToAmbient F (a + b) (homogeneousDualTensorConcat F a b (φ ⊗ₜ[F] ψ)) =
      dualToAmbient F a φ * dualToAmbient F b ψ := by
  have hp : dualToAmbient F a φ ∈ homogeneous F a := ((coefficientSelfDual F a).symm φ).property
  have hq : dualToAmbient F b ψ ∈ homogeneous F b := ((coefficientSelfDual F b).symm ψ).property
  have hm := ambientToDual_mul F a b _ _ hp hq
  rw [ambientToDual_dualToAmbient, ambientToDual_dualToAmbient] at hm
  rw [← hm, dualToAmbient_ambientToDual F (a + b) _ (homogeneous_mul F hp hq)]

/-- A primal homogeneous subspace transported into its actual dual coefficient space. -/
noncomputable def dualCoefficientSpace (n : ℕ) (S : Submodule F (WordAlgebra F)) :
    Submodule F (HomogeneousDual F n) := S.map (ambientToDual F n)

/-- Simple actual dual products belong to the actual tensor-product subspace. -/
theorem actualDualTensorProduct_tmul_mem (a b : ℕ)
    (S : Submodule F (HomogeneousDual F a)) (T : Submodule F (HomogeneousDual F b))
    (φ : HomogeneousDual F a) (ψ : HomogeneousDual F b) (hφ : φ ∈ S) (hψ : ψ ∈ T) :
    homogeneousDualTensorConcat F a b (φ ⊗ₜ[F] ψ) ∈ actualDualTensorProduct F a b S T := by
  refine ⟨φ ⊗ₜ[F] ψ, ⟨(⟨φ, hφ⟩ : S) ⊗ₜ[F] (⟨ψ, hψ⟩ : T), ?_⟩, rfl⟩
  simp only [TensorProduct.map_tmul]
  rfl

/-- Actual primal product-span containment becomes actual dual tensor containment. -/
theorem dualCoefficientSpace_productSpan_le (a b : ℕ)
    (S T : Submodule F (WordAlgebra F))
    (hS : S ≤ homogeneous F a) (hT : T ≤ homogeneous F b) :
    dualCoefficientSpace F (a + b) (productSpan F S T) ≤
      actualDualTensorProduct F a b (dualCoefficientSpace F a S) (dualCoefficientSpace F b T) := by
  rw [dualCoefficientSpace, Submodule.map_le_iff_le_comap, productSpan_le_iff]
  intro P hP Q hQ
  change ambientToDual F (a + b) (P * Q) ∈
    actualDualTensorProduct F a b (dualCoefficientSpace F a S) (dualCoefficientSpace F b T)
  rw [ambientToDual_mul F a b P Q (hS hP) (hT hQ)]
  exact actualDualTensorProduct_tmul_mem F a b
    (dualCoefficientSpace F a S) (dualCoefficientSpace F b T)
    (ambientToDual F a P) (ambientToDual F b Q) ⟨P, hP, rfl⟩ ⟨Q, hQ, rfl⟩

/-- Matrix evaluation of actual dual words, through their actual reconstructed coefficients. -/
noncomputable def actualDualMatrixEvaluation (C : Type*) [CommRing C] [Algebra F C]
    (k n : ℕ) (v : Bool → Matrix (Fin k) (Fin k) C) :
    HomogeneousDual F n →ₗ[F] Matrix (Fin k) (Fin k) C :=
  (CriticalGK2.binaryEvaluation F (Matrix (Fin k) (Fin k) C) v).toLinearMap.comp
    (dualToAmbient F n)

/-- Actual dual evaluation of tensor concatenation is actual matrix multiplication. -/
theorem actualDualMatrixEvaluation_tensorConcat (C : Type*) [CommRing C] [Algebra F C]
    (k a b : ℕ) (v : Bool → Matrix (Fin k) (Fin k) C)
    (φ : HomogeneousDual F a) (ψ : HomogeneousDual F b) :
    actualDualMatrixEvaluation F C k (a + b) v
        (homogeneousDualTensorConcat F a b (φ ⊗ₜ[F] ψ)) =
      actualDualMatrixEvaluation F C k a v φ * actualDualMatrixEvaluation F C k b v ψ := by
  change CriticalGK2.binaryEvaluation F (Matrix (Fin k) (Fin k) C) v
      (dualToAmbient F (a + b) (homogeneousDualTensorConcat F a b (φ ⊗ₜ[F] ψ))) =
    CriticalGK2.binaryEvaluation F (Matrix (Fin k) (Fin k) C) v (dualToAmbient F a φ) *
      CriticalGK2.binaryEvaluation F (Matrix (Fin k) (Fin k) C) v (dualToAmbient F b ψ)
  rw [dualToAmbient_tensorConcat F a b φ ψ]
  exact (CriticalGK2.binaryEvaluation F (Matrix (Fin k) (Fin k) C) v).map_mul _ _

end

end CriticalGK2.Actual
