import CriticalGK2.FreeTailCutSupport
import CriticalGK2.WaitingCutRank

/-!
# Actual common-stem spaces and their full cut supports

The actual coefficient image of the two physical letter blocks is identified
with the range of the actual stem tensor map on the entire degree-one dual
space. At every cut inside the stem, its complete prefix and suffix support
dimensions are proved to be r and 2r, where r is the actual polynomial cut
rank. All outside functionals remain arbitrary throughout this proof.
-/

namespace CriticalGK2.ContractionBudget

noncomputable section

open TensorProduct

variable {F X Y A : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]
  [AddCommGroup A] [Module F A]

theorem contractRight_rightEquiv (e : Y ≃ₗ[F] A) (t : X ⊗[F] Y)
    (eta : Module.Dual F A) :
    contractRight eta (e.lTensor X t) = contractRight (eta.comp e.toLinearMap) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul x y => simp only [LinearEquiv.lTensor_tmul, contractRight_tmul,
      LinearMap.comp_apply, LinearEquiv.coe_coe]

theorem extendedPair_rightEquiv (e : Y ≃ₗ[F] A) (t : X ⊗[F] Y)
    (phi : Module.Dual F X) :
    extendedPair phi (e.lTensor X t) = e (extendedPair phi t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul x y => simp only [LinearEquiv.lTensor_tmul, extendedPair_tmul, map_smul]

theorem tensorPrefixSupport_rightEquiv (e : Y ≃ₗ[F] A)
    (S : Submodule F (X ⊗[F] Y)) :
    tensorPrefixSupport (S.map (e.lTensor X).toLinearMap) = tensorPrefixSupport S := by
  apply le_antisymm
  · refine iSup_le fun eta => ?_
    rintro x ⟨u, ⟨t, ht, rfl⟩, rfl⟩
    rw [LinearEquiv.coe_coe, contractRight_rightEquiv]
    exact contractRight_mem_tensorPrefixSupport S (eta.comp e.toLinearMap) t ht
  · refine iSup_le fun eta => ?_
    rintro x ⟨t, ht, rfl⟩
    have hu : e.lTensor X t ∈ S.map (e.lTensor X).toLinearMap := ⟨t, ht, rfl⟩
    have hc := contractRight_mem_tensorPrefixSupport (S.map (e.lTensor X).toLinearMap)
      (eta.comp e.symm.toLinearMap) _ hu
    have he : (eta.comp e.symm.toLinearMap).comp e.toLinearMap = eta := by
      ext y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [contractRight_rightEquiv, he] at hc
    exact hc

theorem tensorSuffixSupport_rightEquiv (e : Y ≃ₗ[F] A)
    (S : Submodule F (X ⊗[F] Y)) :
    tensorSuffixSupport (S.map (e.lTensor X).toLinearMap) =
      (tensorSuffixSupport S).map e.toLinearMap := by
  apply le_antisymm
  · refine iSup_le fun phi => ?_
    rintro x ⟨u, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨extendedPair phi t, extendedPair_mem_tensorSuffixSupport S phi t ht, ?_⟩
    exact (extendedPair_rightEquiv e t phi).symm
  · rw [Submodule.map_le_iff_le_comap]
    refine iSup_le fun phi => ?_
    rintro x ⟨t, ht, rfl⟩
    have hu : e.lTensor X t ∈ S.map (e.lTensor X).toLinearMap := ⟨t, ht, rfl⟩
    have hc := extendedPair_mem_tensorSuffixSupport (S.map (e.lTensor X).toLinearMap)
      phi _ hu
    rw [extendedPair_rightEquiv] at hc
    exact hc

theorem freeTailTensorSpace_prefixSupport_rightEquiv_finrank {Z : Type*}
    [AddCommGroup Z] [Module F Z] (e : Y ⊗[F] Z ≃ₗ[F] A)
    (t : X ⊗[F] Y) (z0 : Z) (hz0 : z0 ≠ 0) :
    Module.finrank F (tensorPrefixSupport
      ((freeTailTensorSpace (Z := Z) t).map (e.lTensor X).toLinearMap)) = tensorCutRank t := by
  rw [tensorPrefixSupport_rightEquiv]
  exact freeTailTensorSpace_prefixSupport_finrank t z0 hz0

theorem freeTailTensorSpace_suffixSupport_rightEquiv_finrank {Z : Type*}
    [AddCommGroup Z] [Module F Z] [FiniteDimensional F X] [FiniteDimensional F Y]
    [FiniteDimensional F Z] (e : Y ⊗[F] Z ≃ₗ[F] A) (t : X ⊗[F] Y) :
    Module.finrank F (tensorSuffixSupport
      ((freeTailTensorSpace (Z := Z) t).map (e.lTensor X).toLinearMap)) =
        tensorCutRank t * Module.finrank F Z := by
  rw [tensorSuffixSupport_rightEquiv, e.finrank_map_eq]
  exact freeTailTensorSpace_suffixSupport_finrank t

end

end CriticalGK2.ContractionBudget

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct CriticalGK2.ContractionBudget

variable (F : Type*) [Field F]

local instance (n : ℕ) : DecidableEq (LengthWord n) := Classical.decEq _

def actualStemDualMap (q : ℕ) (P : WordAlgebra F) :
    HomogeneousDual F 1 →ₗ[F] HomogeneousDual F (q + 1) :=
  (homogeneousDualTensorConcat F q 1).toLinearMap.comp
    (TensorProduct.mk F (HomogeneousDual F q) (HomogeneousDual F 1) (ambientToDual F q P))

def actualStemDualSpace (q : ℕ) (P : WordAlgebra F) :
    Submodule F (HomogeneousDual F (q + 1)) := LinearMap.range (actualStemDualMap F q P)

theorem homogeneousDual_one_finrank : Module.finrank F (HomogeneousDual F 1) = 2 := by
  rw [← (coefficientSelfDual F 1).finrank_eq, finrank_homogeneous]
  norm_num

theorem ambientToDual_homogeneousWordBasis (n : ℕ) (w : LengthWord n) :
    ambientToDual F n (homogeneousWordBasis F n w).val =
      (homogeneousWordBasis F n).dualBasis w := by
  classical
  change coefficientSelfDual F n
    (homogeneousProjection F n (homogeneousWordBasis F n w).val) = _
  have hp : homogeneousProjection F n (homogeneousWordBasis F n w).val =
      homogeneousWordBasis F n w := by
    apply Subtype.ext
    exact homogeneousProjection_of_mem F n _ (homogeneousWordBasis F n w).property
  rw [hp]
  exact coefficientSelfDual_basis F n w

/-- The two actual coefficient-dual letters span the whole actual degree-one
space. The proof reduces arbitrary actual length-one words to one letter. -/
theorem actualDualLetters_span :
    Submodule.span F (Set.range fun b : Bool => ambientToDual F 1 (binaryLetter F b)) =
      (⊤ : Submodule F (HomogeneousDual F 1)) := by
  classical
  apply top_unique
  rw [← (homogeneousWordBasis F 1).dualBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro phi ⟨w, rfl⟩
  obtain ⟨a, ha⟩ := exists_stemWord_of_length 1 w.val w.property
  have hconst : a = (fun _ : Fin 1 => a 0) := by
    funext i
    exact congrArg a (Subsingleton.elim i 0)
  have hw : FreeMonoid.of (a 0) = w.val := by
    rw [hconst, List.ofFn_const] at ha
    simpa only [List.replicate_succ, List.replicate_zero] using ha
  have he : ambientToDual F 1 (binaryLetter F (a 0)) =
      (homogeneousWordBasis F 1).dualBasis w := by
    have hp : binaryLetter F (a 0) = (homogeneousWordBasis F 1 w).val := by
      rw [homogeneousWordBasis_coe]
      change MonoidAlgebra.single (FreeMonoid.of (a 0)) (1 : F) =
        MonoidAlgebra.single w.val 1
      exact congrArg (fun v : Word => MonoidAlgebra.single v (1 : F)) hw
    calc
      ambientToDual F 1 (binaryLetter F (a 0)) =
          ambientToDual F 1 (homogeneousWordBasis F 1 w).val :=
        congrArg (fun Q : WordAlgebra F => ambientToDual F 1 Q) hp
      _ = (homogeneousWordBasis F 1).dualBasis w := ambientToDual_homogeneousWordBasis F 1 w
  rw [← he]
  exact Submodule.subset_span ⟨a 0, rfl⟩

/-- Exact identification of the source construction's two physical blocks
with the entire actual free one-letter tail. -/
theorem stemSpace_dualCoefficientSpace_eq_actualStemDualSpace
    (n : ℕ) (t : StemWord n → F) :
    dualCoefficientSpace F (n + 1) (stemSpace F n t) =
      actualStemDualSpace F n (stemPolynomial F n t) := by
  have hP : stemPolynomial F n t ∈ homogeneous F n :=
    (wordHomogeneous_iff_mem_homogeneous F n _).mp (stemPolynomial_homogeneous F n t)
  have he : ∀ b : Bool,
      ambientToDual F (n + 1) (stemEmbedding F n t (binaryLetter F b)) =
        actualStemDualMap F n (stemPolynomial F n t) (ambientToDual F 1 (binaryLetter F b)) := by
    intro b
    rw [stemEmbedding_binaryLetter_eq_prefix_mul,
      ambientToDual_mul F n 1 _ _ hP (binaryLetter_mem_homogeneous F b)]
    rfl
  calc
    dualCoefficientSpace F (n + 1) (stemSpace F n t) =
        Submodule.span F (Set.range fun b : Bool =>
          ambientToDual F (n + 1) (stemEmbedding F n t (binaryLetter F b))) := by
      rw [dualCoefficientSpace, stemSpace, Submodule.map_span, ← Set.range_comp]
      rfl
    _ = Submodule.span F (Set.range fun b : Bool =>
        actualStemDualMap F n (stemPolynomial F n t) (ambientToDual F 1 (binaryLetter F b))) := by
      simp only [he]
    _ = (Submodule.span F (Set.range fun b : Bool => ambientToDual F 1 (binaryLetter F b))).map
        (actualStemDualMap F n (stemPolynomial F n t)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = actualStemDualSpace F n (stemPolynomial F n t) := by
      rw [actualDualLetters_span, Submodule.map_top]
      rfl

/-- The actual inside-stem cut space, retaining the literal degree transport
from `(a+b)+1` to `a+(b+1)`. -/
def actualStemInsideCutSpace (a b : ℕ) (P : WordAlgebra F) :
    Submodule F (HomogeneousDual F a ⊗[F] HomogeneousDual F (b + 1)) :=
  (actualStemDualSpace F (a + b) P).map
    ((homogeneousDualTensorConcat F a (b + 1)).symm.toLinearMap.comp
      (homogeneousDualDegreeCast F (Nat.add_assoc a b 1)).toLinearMap)

/-- Every inside-stem cut is exactly the actual free-tail cut tensor space. -/
theorem actualStemInsideCutSpace_eq_freeTail (a b : ℕ) (P : WordAlgebra F) :
    actualStemInsideCutSpace F a b P =
      (freeTailTensorSpace (Z := HomogeneousDual F 1)
        (wordCutTensor F a b (ambientToDual F (a + b) P))).map
          ((homogeneousDualTensorConcat F b 1).lTensor (HomogeneousDual F a)).toLinearMap := by
  have he : ((homogeneousDualTensorConcat F a (b + 1)).symm.toLinearMap.comp
      (homogeneousDualDegreeCast F (Nat.add_assoc a b 1)).toLinearMap).comp
        (actualStemDualMap F (a + b) P) =
      ((homogeneousDualTensorConcat F b 1).lTensor (HomogeneousDual F a)).toLinearMap.comp
        ((TensorProduct.assoc F (HomogeneousDual F a) (HomogeneousDual F b)
          (HomogeneousDual F 1)).toLinearMap.comp
          (TensorProduct.mk F (HomogeneousDual F a ⊗[F] HomogeneousDual F b)
            (HomogeneousDual F 1) (wordCutTensor F a b (ambientToDual F (a + b) P)))) := by
    ext z
    exact wordCutTensor_append F a b 1 (ambientToDual F (a + b) P) z
  unfold actualStemInsideCutSpace actualStemDualSpace freeTailTensorSpace
  rw [← LinearMap.range_comp, he, LinearMap.range_comp]

theorem actualStemInsideCut_prefixSupport_finrank (a b : ℕ) (P : WordAlgebra F) :
    Module.finrank F (tensorPrefixSupport (actualStemInsideCutSpace F a b P)) =
      polynomialCutRank F a b P := by
  rw [actualStemInsideCutSpace_eq_freeTail]
  have hletter : ambientToDual F 1 (binaryLetter F false) ≠ 0 :=
    ambientToDual_ne_zero F 1 _ (binaryLetter_mem_homogeneous F false)
      (binaryLetter_ne_zero F false)
  exact freeTailTensorSpace_prefixSupport_rightEquiv_finrank (F := F)
    (X := HomogeneousDual F a) (Y := HomogeneousDual F b) (Z := HomogeneousDual F 1)
    (A := HomogeneousDual F (b + 1)) (homogeneousDualTensorConcat F b 1)
    (wordCutTensor F a b (ambientToDual F (a + b) P)) _ hletter

theorem actualStemInsideCut_suffixSupport_finrank (a b : ℕ) (P : WordAlgebra F) :
    Module.finrank F (tensorSuffixSupport (actualStemInsideCutSpace F a b P)) =
      2 * polynomialCutRank F a b P := by
  classical
  letI : FiniteDimensional F (HomogeneousDual F a) :=
    (homogeneousWordBasis F a).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (HomogeneousDual F b) :=
    (homogeneousWordBasis F b).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (HomogeneousDual F 1) :=
    (homogeneousWordBasis F 1).dualBasis.finiteDimensional_of_finite
  rw [actualStemInsideCutSpace_eq_freeTail]
  have h := freeTailTensorSpace_suffixSupport_rightEquiv_finrank (F := F)
    (X := HomogeneousDual F a) (Y := HomogeneousDual F b) (Z := HomogeneousDual F 1)
    (A := HomogeneousDual F (b + 1)) (homogeneousDualTensorConcat F b 1)
      (wordCutTensor F a b (ambientToDual F (a + b) P))
  rw [homogeneousDual_one_finrank] at h
  exact h.trans (Nat.mul_comm _ _)

theorem actualStemDualSpace_finrank (q : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F q) (hP0 : P ≠ 0) :
    Module.finrank F (actualStemDualSpace F q P) = 2 := by
  have hp : ambientToDual F q P ≠ 0 := ambientToDual_ne_zero F q P hP hP0
  have hinj : Function.Injective (actualStemDualMap F q P) :=
    (homogeneousDualTensorConcat F q 1).injective.comp (fixed_left_tensor_injective _ hp)
  rw [actualStemDualSpace, LinearMap.finrank_range_of_inj hinj, homogeneousDual_one_finrank]

#print axioms CriticalGK2.Actual.stemSpace_dualCoefficientSpace_eq_actualStemDualSpace
#print axioms CriticalGK2.Actual.actualStemInsideCut_suffixSupport_finrank

end

end CriticalGK2.Actual
