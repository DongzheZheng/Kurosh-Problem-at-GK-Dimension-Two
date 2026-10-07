import CriticalGK2.RootAlignedContractionBridge
import CriticalGK2.ActualBlockMatrixKernel
import CriticalGK2.DualStageSteps
import CriticalGK2.DualFamilyBridge
import CriticalGK2.BlockTensorSupport

/-!
# Actual long completion annihilators have zero matrix evaluation

The only family inputs are actual homogeneity and actual consecutive product
containment. A single actual polynomial block space lying in a matrix kernel
then forces every sufficiently long left and right completion annihilator into
the actual dual-word matrix kernel. Full arbitrary exterior functionals are
covered by the root contraction span.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F : Type*) [Field F]

/-- The exact degree inverse commutes with actual coefficient-space transport. -/
theorem dualCoefficientSpace_comap_degreeCast {a b : ℕ} (hab : a = b)
    (S : Submodule F (WordAlgebra F)) :
    (dualCoefficientSpace F b S).comap (homogeneousDualDegreeCast F hab).toLinearMap =
      dualCoefficientSpace F a S := by
  subst b
  simp [homogeneousDualDegreeCast]

/-- Every dyadic block no longer than n lies below the actual strict root. -/
theorem dyadic_level_le_strictRoot (H n : ℕ) (hblock : 2 ^ H ≤ n) :
    H ≤ strictDyadicRoot n := by
  by_contra h
  have hroot : strictDyadicRoot n ≤ H := by omega
  have hp : (2 : ℕ) ^ strictDyadicRoot n ≤ 2 ^ H :=
    pow_le_pow_right₀ (by norm_num) hroot
  have hn := degree_lt_strictDyadicPower n
  omega

/-- Actual future polynomial blocks retain a complete first old block. -/
theorem coherent_family_first_block_le (S : ℕ → Submodule F (WordAlgebra F))
    (hS : ∀ h, S h ≤ homogeneous F (2 ^ h))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h))
    (H T : ℕ) (hHT : H ≤ T) :
    S T ≤ productSpan F (S H) (homogeneous F (2 ^ T - 2 ^ H)) := by
  have hadd : H + (T - H) = T := Nat.add_sub_of_le hHT
  have hp : 0 < (2 : ℕ) ^ (T - H) := pow_pos (by norm_num) _
  have hdec : 2 ^ (T - H) = (2 ^ (T - H) - 1) + 1 := by omega
  have hdegree : (2 ^ (T - H) - 1) * 2 ^ H = 2 ^ T - 2 ^ H := by
    rw [Nat.sub_mul, one_mul]
    have hmul : (2 : ℕ) ^ (T - H) * 2 ^ H = 2 ^ T := by
      rw [Nat.mul_comm, ← pow_add, hadd]
    rw [hmul]
  have htail := blockPower_le_homogeneous F (S H) (2 ^ H) (hS H) (2 ^ (T - H) - 1)
  rw [hdegree] at htail
  have hfuture := coherent_family_le_blockPower F S hproduct H (T - H)
  rw [hadd, hdec, blockPower_left_split] at hfuture
  exact hfuture.trans (productSpan_mono F le_rfl htail)

/-- The same actual future blocks retain a complete final old block. -/
theorem coherent_family_last_block_le (S : ℕ → Submodule F (WordAlgebra F))
    (hS : ∀ h, S h ≤ homogeneous F (2 ^ h))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h))
    (H T : ℕ) (hHT : H ≤ T) :
    S T ≤ productSpan F (homogeneous F (2 ^ T - 2 ^ H)) (S H) := by
  have hadd : H + (T - H) = T := Nat.add_sub_of_le hHT
  have hp : 0 < (2 : ℕ) ^ (T - H) := pow_pos (by norm_num) _
  have hdec : 2 ^ (T - H) = (2 ^ (T - H) - 1) + 1 := by omega
  have hdegree : (2 ^ (T - H) - 1) * 2 ^ H = 2 ^ T - 2 ^ H := by
    rw [Nat.sub_mul, one_mul]
    have hmul : (2 : ℕ) ^ (T - H) * 2 ^ H = 2 ^ T := by
      rw [Nat.mul_comm, ← pow_add, hadd]
    rw [hmul]
  have htail := blockPower_le_homogeneous F (S H) (2 ^ H) (hS H) (2 ^ (T - H) - 1)
  rw [hdegree] at htail
  have hfuture := coherent_family_le_blockPower F S hproduct H (T - H)
  rw [hadd, hdec, blockPower_succ] at hfuture
  exact hfuture.trans (productSpan_mono F htail le_rfl)

/-- The complete first-block tensor support admits an arbitrary actual
splitting of its entire tail into retained and exterior degrees. -/
theorem actualDualTensorProduct_le_leftBlockTripleSpace (a b c : ℕ)
    (W : Submodule F (HomogeneousDual F a)) (T : Submodule F (HomogeneousDual F (b + c))) :
    actualDualTensorProduct F a (b + c) W T ≤ actualLeftBlockTripleSpace F a b c W := by
  rintro φ ⟨w, ⟨u, rfl⟩, rfl⟩
  let f : T →ₗ[F] (HomogeneousDual F b ⊗[F] HomogeneousDual F c) :=
    (homogeneousDualTensorConcat F b c).symm.toLinearMap.comp T.subtype
  refine ⟨W.subtype.rTensor (HomogeneousDual F b ⊗[F] HomogeneousDual F c)
      (f.lTensor W u), ⟨f.lTensor W u, rfl⟩, ?_⟩
  change homogeneousDualTripleConcat F a b c
      (W.subtype.rTensor (HomogeneousDual F b ⊗[F] HomogeneousDual F c) (f.lTensor W u)) =
    homogeneousDualTensorConcat F a (b + c) (TensorProduct.map W.subtype T.subtype u)
  induction u using TensorProduct.induction_on with
  | zero =>
      rw [(f.lTensor W).map_zero,
        (W.subtype.rTensor (HomogeneousDual F b ⊗[F] HomogeneousDual F c)).map_zero,
        (TensorProduct.map W.subtype T.subtype).map_zero,
        (homogeneousDualTripleConcat F a b c).map_zero,
        (homogeneousDualTensorConcat F a (b + c)).map_zero]
  | add u v hu hv =>
      rw [(f.lTensor W).map_add,
        (W.subtype.rTensor (HomogeneousDual F b ⊗[F] HomogeneousDual F c)).map_add,
        (homogeneousDualTripleConcat F a b c).map_add,
        (TensorProduct.map W.subtype T.subtype).map_add,
        (homogeneousDualTensorConcat F a (b + c)).map_add, hu, hv]
  | tmul v t =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
        f, LinearMap.comp_apply, LinearEquiv.coe_coe, homogeneousDualTripleConcat,
        LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul, LinearEquiv.apply_symm_apply]

/-- The mirror arbitrary splitting before a complete final actual word block. -/
theorem actualDualTensorProduct_le_rightBlockTripleSpaceLeftAssociated (a b c : ℕ)
    (T : Submodule F (HomogeneousDual F (a + b))) (W : Submodule F (HomogeneousDual F c)) :
    actualDualTensorProduct F (a + b) c T W ≤
      actualRightBlockTripleSpaceLeftAssociated F a b c W := by
  rintro φ ⟨w, ⟨u, rfl⟩, rfl⟩
  let f : T →ₗ[F] (HomogeneousDual F a ⊗[F] HomogeneousDual F b) :=
    (homogeneousDualTensorConcat F a b).symm.toLinearMap.comp T.subtype
  refine ⟨W.subtype.lTensor (HomogeneousDual F a ⊗[F] HomogeneousDual F b)
      (f.rTensor W u), ⟨f.rTensor W u, rfl⟩, ?_⟩
  change homogeneousDualTripleConcatLeft F a b c
      (W.subtype.lTensor (HomogeneousDual F a ⊗[F] HomogeneousDual F b) (f.rTensor W u)) =
    homogeneousDualTensorConcat F (a + b) c (TensorProduct.map T.subtype W.subtype u)
  induction u using TensorProduct.induction_on with
  | zero =>
      rw [(f.rTensor W).map_zero,
        (W.subtype.lTensor (HomogeneousDual F a ⊗[F] HomogeneousDual F b)).map_zero,
        (TensorProduct.map T.subtype W.subtype).map_zero,
        (homogeneousDualTripleConcatLeft F a b c).map_zero,
        (homogeneousDualTensorConcat F (a + b) c).map_zero]
  | add u v hu hv =>
      rw [(f.rTensor W).map_add,
        (W.subtype.lTensor (HomogeneousDual F a ⊗[F] HomogeneousDual F b)).map_add,
        (homogeneousDualTripleConcatLeft F a b c).map_add,
        (TensorProduct.map T.subtype W.subtype).map_add,
        (homogeneousDualTensorConcat F (a + b) c).map_add, hu, hv]
  | tmul t v =>
      simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
        f, LinearMap.comp_apply, LinearEquiv.coe_coe, homogeneousDualTripleConcatLeft,
        LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul, LinearEquiv.apply_symm_apply]

/-- Actual future root support needed for retaining a complete first event block. -/
theorem actualDualFamily_prefixRoot_support (S : ℕ → Submodule F (WordAlgebra F))
    (hS : ∀ h, S h ≤ homogeneous F (2 ^ h))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h)) (H r : ℕ) :
    (actualDualFamily F S (strictDyadicRoot (2 ^ H + r))).comap
        (homogeneousDualDegreeCast F (actualRootPrefixAlignmentDegree (2 ^ H) r)).toLinearMap ≤
      actualLeftBlockTripleSpace F (2 ^ H) r
        (2 ^ strictDyadicRoot (2 ^ H + r) - (2 ^ H + r)) (actualDualFamily F S H) := by
  let T := strictDyadicRoot (2 ^ H + r)
  have hlevel : H ≤ T := dyadic_level_le_strictRoot H (2 ^ H + r) (by omega)
  have hdegree : 2 ^ T - 2 ^ H = r + (2 ^ T - (2 ^ H + r)) := by
    have hp := degree_lt_strictDyadicPower (2 ^ H + r)
    dsimp only [T]
    omega
  have hfirst := coherent_family_first_block_le F S hS hproduct H T hlevel
  rw [hdegree] at hfirst
  change (dualCoefficientSpace F (2 ^ T) (S T)).comap
      (homogeneousDualDegreeCast F (actualRootPrefixAlignmentDegree (2 ^ H) r)).toLinearMap ≤ _
  rw [dualCoefficientSpace_comap_degreeCast]
  exact (Submodule.map_mono hfirst).trans
    ((dualCoefficientSpace_productSpan_le F (2 ^ H)
      (r + (2 ^ T - (2 ^ H + r))) (S H) (homogeneous F (r + (2 ^ T - (2 ^ H + r))))
      (hS H) le_rfl).trans
      (actualDualTensorProduct_le_leftBlockTripleSpace F (2 ^ H) r
        (2 ^ T - (2 ^ H + r)) (actualDualFamily F S H) _))

/-- Actual future root support needed for retaining a complete final event block. -/
theorem actualDualFamily_suffixRoot_support (S : ℕ → Submodule F (WordAlgebra F))
    (hS : ∀ h, S h ≤ homogeneous F (2 ^ h))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h)) (H r : ℕ) :
    (actualDualFamily F S (strictDyadicRoot (r + 2 ^ H))).comap
        (homogeneousDualDegreeCast F (actualRootSuffixAlignmentDegree r (2 ^ H))).toLinearMap ≤
      actualRightBlockTripleSpaceLeftAssociated F
        (2 ^ strictDyadicRoot (r + 2 ^ H) - (r + 2 ^ H)) r (2 ^ H) (actualDualFamily F S H) := by
  let T := strictDyadicRoot (r + 2 ^ H)
  have hlevel : H ≤ T := dyadic_level_le_strictRoot H (r + 2 ^ H) (by omega)
  have hdegree : 2 ^ T - 2 ^ H = (2 ^ T - (r + 2 ^ H)) + r := by
    have hp := degree_lt_strictDyadicPower (r + 2 ^ H)
    dsimp only [T]
    omega
  have hlast := coherent_family_last_block_le F S hS hproduct H T hlevel
  rw [hdegree] at hlast
  change (dualCoefficientSpace F (2 ^ T) (S T)).comap
      (homogeneousDualDegreeCast F (actualRootSuffixAlignmentDegree r (2 ^ H))).toLinearMap ≤ _
  rw [dualCoefficientSpace_comap_degreeCast]
  exact (Submodule.map_mono hlast).trans
    ((dualCoefficientSpace_productSpan_le F
      ((2 ^ T - (r + 2 ^ H)) + r) (2 ^ H)
      (homogeneous F ((2 ^ T - (r + 2 ^ H)) + r)) (S H) le_rfl (hS H)).trans
      (actualDualTensorProduct_le_rightBlockTripleSpaceLeftAssociated F
        (2 ^ T - (r + 2 ^ H)) r (2 ^ H) _ (actualDualFamily F S H)))

/-- Every whole-exterior prefix contraction of a future actual root has zero
matrix evaluation once a complete actual event block has zero evaluation. -/
theorem actualDualFamily_rightCompletion_dualAnnihilator_le_matrix_kernel
    (C : Type*) [CommRing C] [Algebra F C] (k : ℕ)
    (v : Bool → Matrix (Fin k) (Fin k) C) (S : ℕ → Submodule F (WordAlgebra F))
    (hS : ∀ h, S h ≤ homogeneous F (2 ^ h))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h)) (H r : ℕ)
    (hker : S H ≤ LinearMap.ker
      (CriticalGK2.binaryEvaluation F (Matrix (Fin k) (Fin k) C) v).toLinearMap) :
    (homogeneousRightCompletion F (actualDualFamily F S) (2 ^ H + r)).dualAnnihilator ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k (2 ^ H + r) v) := by
  have hpositive : 0 < (2 : ℕ) ^ H := pow_pos (by norm_num) _
  have hn : 2 ^ H + r ≠ 0 := by omega
  have hW : actualDualFamily F S H ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k (2 ^ H) v) :=
    dualCoefficientSpace_le_matrix_kernel F C k (2 ^ H) v (S H) (hS H) hker
  rw [homogeneousRightCompletion_dualAnnihilator F _ _ hn,
    actualRootPrefixContractionSupport]
  refine iSup_le fun η => ?_
  rintro θ ⟨φ, hφ, rfl⟩
  let z := (homogeneousDualDegreeCast F (actualRootPrefixAlignmentDegree (2 ^ H) r)).symm φ
  have hcasteq : homogeneousDualDegreeCast F (actualRootPrefixAlignmentDegree (2 ^ H) r) z = φ :=
    LinearEquiv.apply_symm_apply _ _
  have hz : z ∈ actualLeftBlockTripleSpace F (2 ^ H) r
      (2 ^ strictDyadicRoot (2 ^ H + r) - (2 ^ H + r)) (actualDualFamily F S H) := by
    apply actualDualFamily_prefixRoot_support F S hS hproduct H r
    change homogeneousDualDegreeCast F (actualRootPrefixAlignmentDegree (2 ^ H) r) z ∈
      actualDualFamily F S (strictDyadicRoot (2 ^ H + r))
    rw [hcasteq]
    exact hφ
  change actualDualMatrixEvaluation F C k (2 ^ H + r) v
    (actualRootPrefixContraction F (2 ^ H + r) η φ) = 0
  have heq := actualRootPrefixContraction_eq_actualPrefixContraction F (2 ^ H) r η
    (actualRootPrefixAlignmentDegree (2 ^ H) r) z
  rw [hcasteq] at heq
  rw [heq]
  exact actualPrefixContraction_matrix_evaluation_eq_zero F C k (2 ^ H) r
    (2 ^ strictDyadicRoot (2 ^ H + r) - (2 ^ H + r)) v (actualDualFamily F S H) hW η z hz

/-- The mirror result for every whole-exterior suffix contraction. -/
theorem actualDualFamily_leftCompletion_dualAnnihilator_le_matrix_kernel
    (C : Type*) [CommRing C] [Algebra F C] (k : ℕ)
    (v : Bool → Matrix (Fin k) (Fin k) C) (S : ℕ → Submodule F (WordAlgebra F))
    (hS : ∀ h, S h ≤ homogeneous F (2 ^ h))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h)) (H r : ℕ)
    (hker : S H ≤ LinearMap.ker
      (CriticalGK2.binaryEvaluation F (Matrix (Fin k) (Fin k) C) v).toLinearMap) :
    (homogeneousLeftCompletion F (actualDualFamily F S) (r + 2 ^ H)).dualAnnihilator ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k (r + 2 ^ H) v) := by
  have hpositive : 0 < (2 : ℕ) ^ H := pow_pos (by norm_num) _
  have hn : r + 2 ^ H ≠ 0 := by omega
  have hW : actualDualFamily F S H ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k (2 ^ H) v) :=
    dualCoefficientSpace_le_matrix_kernel F C k (2 ^ H) v (S H) (hS H) hker
  rw [homogeneousLeftCompletion_dualAnnihilator F _ _ hn,
    actualRootSuffixContractionSupport]
  refine iSup_le fun η => ?_
  rintro θ ⟨φ, hφ, rfl⟩
  let z := (homogeneousDualDegreeCast F (actualRootSuffixAlignmentDegree r (2 ^ H))).symm φ
  have hcasteq : homogeneousDualDegreeCast F (actualRootSuffixAlignmentDegree r (2 ^ H)) z = φ :=
    LinearEquiv.apply_symm_apply _ _
  have hz : z ∈ actualRightBlockTripleSpaceLeftAssociated F
      (2 ^ strictDyadicRoot (r + 2 ^ H) - (r + 2 ^ H)) r (2 ^ H) (actualDualFamily F S H) := by
    apply actualDualFamily_suffixRoot_support F S hS hproduct H r
    change homogeneousDualDegreeCast F (actualRootSuffixAlignmentDegree r (2 ^ H)) z ∈
      actualDualFamily F S (strictDyadicRoot (r + 2 ^ H))
    rw [hcasteq]
    exact hφ
  change actualDualMatrixEvaluation F C k (r + 2 ^ H) v
    (actualRootSuffixContraction F (r + 2 ^ H) η φ) = 0
  have heq := actualRootSuffixContraction_eq_actualSuffixContractionLeftAssociated F r (2 ^ H) η
    (actualRootSuffixAlignmentDegree r (2 ^ H)) z
  rw [hcasteq] at heq
  rw [heq]
  exact actualSuffixContractionLeftAssociated_matrix_evaluation_eq_zero F C k
    (2 ^ strictDyadicRoot (r + 2 ^ H) - (r + 2 ^ H)) r (2 ^ H) v
    (actualDualFamily F S H) hW η z hz

/-- Actual right completion annihilators of every length at least the event
block length evaluate to zero. -/
theorem actualDualFamily_rightCompletion_dualAnnihilator_le_matrix_kernel_of_ge
    (C : Type*) [CommRing C] [Algebra F C] (k : ℕ)
    (v : Bool → Matrix (Fin k) (Fin k) C) (S : ℕ → Submodule F (WordAlgebra F))
    (hS : ∀ h, S h ≤ homogeneous F (2 ^ h))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h)) (H n : ℕ)
    (hker : S H ≤ LinearMap.ker
      (CriticalGK2.binaryEvaluation F (Matrix (Fin k) (Fin k) C) v).toLinearMap)
    (hn : 2 ^ H ≤ n) :
    (homogeneousRightCompletion F (actualDualFamily F S) n).dualAnnihilator ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k n v) := by
  have hdegree : 2 ^ H + (n - 2 ^ H) = n := by omega
  have h := actualDualFamily_rightCompletion_dualAnnihilator_le_matrix_kernel F C k v S hS hproduct H
    (n - 2 ^ H) hker
  rw [hdegree] at h
  exact h

/-- Actual left completion annihilators have the same unconditional long
length threshold. -/
theorem actualDualFamily_leftCompletion_dualAnnihilator_le_matrix_kernel_of_ge
    (C : Type*) [CommRing C] [Algebra F C] (k : ℕ)
    (v : Bool → Matrix (Fin k) (Fin k) C) (S : ℕ → Submodule F (WordAlgebra F))
    (hS : ∀ h, S h ≤ homogeneous F (2 ^ h))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h)) (H n : ℕ)
    (hker : S H ≤ LinearMap.ker
      (CriticalGK2.binaryEvaluation F (Matrix (Fin k) (Fin k) C) v).toLinearMap)
    (hn : 2 ^ H ≤ n) :
    (homogeneousLeftCompletion F (actualDualFamily F S) n).dualAnnihilator ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k n v) := by
  have hdegree : (n - 2 ^ H) + 2 ^ H = n := by omega
  have h := actualDualFamily_leftCompletion_dualAnnihilator_le_matrix_kernel F C k v S hS hproduct H
    (n - 2 ^ H) hker
  rw [hdegree] at h
  exact h

end

end CriticalGK2.Actual
