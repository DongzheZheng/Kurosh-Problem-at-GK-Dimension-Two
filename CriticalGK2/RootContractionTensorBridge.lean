import CriticalGK2.RootContractionDuality
import CriticalGK2.DualDegreeBridge
import CriticalGK2.LongCut

/-!
# Whole-functional root contractions are actual tensor contractions

The dual of the actual completion test map is identified with contraction of
the actual dual word tensor concatenation. The proof uses the proved primal
and dual product pairing and finite evaluation duality. Dual concatenation
associativity follows
from exact reconstruction and associativity of the original polynomial product.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F : Type*) [Field F]

/-- The actual dual coefficient reconstruction is genuinely injective. -/
theorem dualToAmbient_injective (n : ℕ) : Function.Injective (dualToAmbient F n) := by
  intro φ ψ h
  have heq := congrArg (ambientToDual F n) h
  simpa only [ambientToDual_dualToAmbient] using heq

/-- Actual dual tensor multiplication is associative after its literal degree cast. -/
theorem homogeneousDualTensorConcat_associative (a b c : ℕ)
    (φ : HomogeneousDual F a) (ψ : HomogeneousDual F b) (θ : HomogeneousDual F c) :
    homogeneousDualDegreeCast F (Nat.add_assoc a b c)
      (homogeneousDualTensorConcat F (a + b) c
        (homogeneousDualTensorConcat F a b (φ ⊗ₜ[F] ψ) ⊗ₜ[F] θ)) =
      homogeneousDualTensorConcat F a (b + c)
        (φ ⊗ₜ[F] homogeneousDualTensorConcat F b c (ψ ⊗ₜ[F] θ)) := by
  apply dualToAmbient_injective F (a + (b + c))
  rw [dualToAmbient_degreeCast, dualToAmbient_tensorConcat,
    dualToAmbient_tensorConcat, dualToAmbient_tensorConcat, dualToAmbient_tensorConcat]
  exact mul_assoc _ _ _

/-- Whole-exterior prefix contraction acts on actual dual simple tensors by
applying the external functional to the entire last factor. -/
theorem actualRootPrefixContraction_tensorConcat_tmul (n : ℕ)
    (η : Module.Dual F (HomogeneousDual F (2 ^ strictDyadicRoot n - n)))
    (φ : HomogeneousDual F n) (ψ : HomogeneousDual F (2 ^ strictDyadicRoot n - n)) :
    actualRootPrefixContraction F n η
      (homogeneousDualDegreeCast F (completionRootDegree n)
        (homogeneousDualTensorConcat F n (2 ^ strictDyadicRoot n - n) (φ ⊗ₜ[F] ψ))) =
      η ψ • φ := by
  let y := (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n))).symm η
  apply LinearMap.ext
  intro x
  have htest : rightCompletionTestMap F n y x =
      homogeneousDegreeCast F (completionRootDegree n)
        (homogeneousMultiplication F n (2 ^ strictDyadicRoot n - n) x y) := by
    apply Subtype.ext
    rw [homogeneousDegreeCast_coe]
    rfl
  change (homogeneousDualDegreeCast F (completionRootDegree n)
    (homogeneousDualTensorConcat F n (2 ^ strictDyadicRoot n - n) (φ ⊗ₜ[F] ψ)))
      (rightCompletionTestMap F n y x) = η ψ * φ x
  rw [htest, homogeneousDualDegreeCast_pairing,
    ← homogeneousTensorConcat_tmul, homogeneousDualTensorConcat_pairing]
  rw [show ψ y = η ψ from Module.apply_evalEquiv_symm_apply F _ ψ η]
  exact mul_comm _ _

/-- Whole-exterior suffix contraction acts on actual dual simple tensors by
applying the external functional to the entire first factor. -/
theorem actualRootSuffixContraction_tensorConcat_tmul (n : ℕ)
    (η : Module.Dual F (HomogeneousDual F (2 ^ strictDyadicRoot n - n)))
    (φ : HomogeneousDual F (2 ^ strictDyadicRoot n - n)) (ψ : HomogeneousDual F n) :
    actualRootSuffixContraction F n η
      (homogeneousDualDegreeCast F (completionRootDegreeLeft n)
        (homogeneousDualTensorConcat F (2 ^ strictDyadicRoot n - n) n (φ ⊗ₜ[F] ψ))) =
      η φ • ψ := by
  let y := (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n))).symm η
  apply LinearMap.ext
  intro x
  have htest : leftCompletionTestMap F n y x =
      homogeneousDegreeCast F (completionRootDegreeLeft n)
        (homogeneousMultiplication F (2 ^ strictDyadicRoot n - n) n y x) := by
    apply Subtype.ext
    rw [homogeneousDegreeCast_coe]
    rfl
  change (homogeneousDualDegreeCast F (completionRootDegreeLeft n)
    (homogeneousDualTensorConcat F (2 ^ strictDyadicRoot n - n) n (φ ⊗ₜ[F] ψ)))
      (leftCompletionTestMap F n y x) = η φ * ψ x
  rw [htest, homogeneousDualDegreeCast_pairing,
    ← homogeneousTensorConcat_tmul, homogeneousDualTensorConcat_pairing]
  rw [show φ y = η φ from Module.apply_evalEquiv_symm_apply F _ φ η]

/-- Prefix completion contractions equal the existing actual tensor
contraction for arbitrary tensors, not only pure external vectors. -/
theorem actualRootPrefixContraction_tensorConcat (n : ℕ)
    (η : Module.Dual F (HomogeneousDual F (2 ^ strictDyadicRoot n - n)))
    (z : HomogeneousDual F n ⊗[F] HomogeneousDual F (2 ^ strictDyadicRoot n - n)) :
    actualRootPrefixContraction F n η
      (homogeneousDualDegreeCast F (completionRootDegree n)
        (homogeneousDualTensorConcat F n (2 ^ strictDyadicRoot n - n) z)) =
      CriticalGK2.contractRight η z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [(homogeneousDualTensorConcat F n (2 ^ strictDyadicRoot n - n)).map_zero,
        (homogeneousDualDegreeCast F (completionRootDegree n)).map_zero,
        (actualRootPrefixContraction F n η).map_zero,
        (CriticalGK2.contractRight η).map_zero]
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul φ ψ =>
      rw [actualRootPrefixContraction_tensorConcat_tmul, CriticalGK2.contractRight_tmul]

/-- The corresponding suffix identification with contraction of the whole first factor. -/
theorem actualRootSuffixContraction_tensorConcat (n : ℕ)
    (η : Module.Dual F (HomogeneousDual F (2 ^ strictDyadicRoot n - n)))
    (z : HomogeneousDual F (2 ^ strictDyadicRoot n - n) ⊗[F] HomogeneousDual F n) :
    actualRootSuffixContraction F n η
      (homogeneousDualDegreeCast F (completionRootDegreeLeft n)
        (homogeneousDualTensorConcat F (2 ^ strictDyadicRoot n - n) n z)) =
      CriticalGK2.extendedPair η z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [(homogeneousDualTensorConcat F (2 ^ strictDyadicRoot n - n) n).map_zero,
        (homogeneousDualDegreeCast F (completionRootDegreeLeft n)).map_zero,
        (actualRootSuffixContraction F n η).map_zero,
        (CriticalGK2.extendedPair η).map_zero]
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul φ ψ =>
      rw [actualRootSuffixContraction_tensorConcat_tmul, CriticalGK2.extendedPair_tmul]

/-- Actual root prefix contraction is obtained by the exact degree and tensor inverses. -/
theorem actualRootPrefixContraction_eq_contractRight (n : ℕ)
    (η : Module.Dual F (HomogeneousDual F (2 ^ strictDyadicRoot n - n)))
    (φ : HomogeneousDual F (2 ^ strictDyadicRoot n)) :
    actualRootPrefixContraction F n η φ =
      CriticalGK2.contractRight η
        ((homogeneousDualTensorConcat F n (2 ^ strictDyadicRoot n - n)).symm
          ((homogeneousDualDegreeCast F (completionRootDegree n)).symm φ)) := by
  have h := actualRootPrefixContraction_tensorConcat F n η
    ((homogeneousDualTensorConcat F n (2 ^ strictDyadicRoot n - n)).symm
      ((homogeneousDualDegreeCast F (completionRootDegree n)).symm φ))
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- Actual root suffix contraction is obtained by the exact degree and tensor inverses. -/
theorem actualRootSuffixContraction_eq_extendedPair (n : ℕ)
    (η : Module.Dual F (HomogeneousDual F (2 ^ strictDyadicRoot n - n)))
    (φ : HomogeneousDual F (2 ^ strictDyadicRoot n)) :
    actualRootSuffixContraction F n η φ =
      CriticalGK2.extendedPair η
        ((homogeneousDualTensorConcat F (2 ^ strictDyadicRoot n - n) n).symm
          ((homogeneousDualDegreeCast F (completionRootDegreeLeft n)).symm φ)) := by
  have h := actualRootSuffixContraction_tensorConcat F n η
    ((homogeneousDualTensorConcat F (2 ^ strictDyadicRoot n - n) n).symm
      ((homogeneousDualDegreeCast F (completionRootDegreeLeft n)).symm φ))
  simpa only [LinearEquiv.apply_symm_apply] using h

end

end CriticalGK2.Actual
