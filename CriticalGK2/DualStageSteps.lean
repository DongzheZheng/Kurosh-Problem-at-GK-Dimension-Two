import CriticalGK2.ActualLocalPI
import CriticalGK2.PolynomialStages
import CriticalGK2.DualDegreeBridge

/-!
# Actual dual waiting and reset stage inclusions

All stage spaces here are images of the actual two physical common-prefix
blocks. The degree changes are literal degree transports, and all inclusions
are derived from actual polynomial multiplication. The reset kernel is proved
for the actual dual-word matrix evaluation over any commutative coefficient
algebra.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- The complete actual dual space spanned by the two physical stem blocks. -/
def actualStemBlockSpace (n : ℕ) (t : CriticalGK2.StemWord n → F) :
    Submodule F (HomogeneousDual F (n + 1)) :=
  dualCoefficientSpace F (n + 1) (stemSpace F n t)

@[simp]
theorem actualBlockPowerSpace_one (n : ℕ) (t : CriticalGK2.StemWord n → F) :
    (actualBlockPowerSpace F n t 1).map
      (homogeneousDualDegreeCast F (one_mul (n + 1))).toLinearMap =
      actualStemBlockSpace F n t := by
  change (dualCoefficientSpace F (1 * (n + 1)) (blockPower F (stemSpace F n t) 1)).map
    (homogeneousDualDegreeCast F (one_mul (n + 1))).toLinearMap = _
  rw [← dualCoefficientSpace_degreeCast F (one_mul (n + 1))]
  simp only [blockPower_one, actualStemBlockSpace]

/-- Every stage's actual two-block dual configuration is nonzero. -/
theorem actualStemBlockSpace_ne_bot (n : ℕ) (t : CriticalGK2.StemWord n → F)
    (ht : t ≠ 0) : actualStemBlockSpace F n t ≠ ⊥ :=
  dualCoefficientSpace_ne_bot F (n + 1) (stemSpace F n t)
    (stemSpace_le_homogeneous F n t) (stemSpace_ne_bot F n t ht)

/-- The waiting operation gives the actual next dual space inside the full
actual tensor square of the old dual space, with its exact degree transport. -/
theorem actualWaitingSpace_le_tensorSquare (n : ℕ) (t : CriticalGK2.StemWord n → F)
    (hdegree : (n + 1) + (n + 1) = (2 * n + 1) + 1) :
    actualStemBlockSpace F (2 * n + 1) (waitingCoefficients F n t) ≤
      (actualDualTensorProduct F (n + 1) (n + 1)
        (actualStemBlockSpace F n t) (actualStemBlockSpace F n t)).map
        (homogeneousDualDegreeCast F hdegree).toLinearMap := by
  change dualCoefficientSpace F ((2 * n + 1) + 1)
      (stemSpace F (2 * n + 1) (waitingCoefficients F n t)) ≤ _
  rw [dualCoefficientSpace_degreeCast F hdegree]
  apply Submodule.map_mono
  exact (Submodule.map_mono (waitingSpace_le_product F n t)).trans
    (dualCoefficientSpace_productSpan_le F (n + 1) (n + 1)
      (stemSpace F n t) (stemSpace F n t)
      (stemSpace_le_homogeneous F n t) (stemSpace_le_homogeneous F n t))

/-- Resetting gives a nonzero new configuration inside the complete
old block-power space. -/
theorem actualResetSpace_le_blockPower (n : ℕ) (t : CriticalGK2.StemWord n → F)
    (k : ℕ) (u : FreeMonoid Bool)
    (hdegree : (((k * k + 1) * (k * k + 1) + u.length) + 1) * (n + 1) =
      CriticalGK2.localResetDegree n k u + 1) :
    actualStemBlockSpace F (CriticalGK2.localResetDegree n k u)
      (CriticalGK2.localResetCoefficients F n t k u) ≤
      (actualBlockPowerSpace F n t (((k * k + 1) * (k * k + 1) + u.length) + 1)).map
        (homogeneousDualDegreeCast F hdegree).toLinearMap := by
  change dualCoefficientSpace F (CriticalGK2.localResetDegree n k u + 1)
      (stemSpace F (CriticalGK2.localResetDegree n k u)
        (CriticalGK2.localResetCoefficients F n t k u)) ≤ _
  rw [dualCoefficientSpace_degreeCast F hdegree]
  exact Submodule.map_mono (Submodule.map_mono (resetSpace_le_blockPower F n t k u))

/-- An actual homogeneous primal matrix kernel transports to the actual dual
matrix kernel through the proved exact coefficient inverse. -/
theorem dualCoefficientSpace_le_matrix_kernel (C : Type*) [CommRing C] [Algebra F C]
    (k n : ℕ) (v : Bool → Matrix (Fin k) (Fin k) C)
    (S : Submodule F (WordAlgebra F)) (hS : S ≤ homogeneous F n)
    (hker : S ≤ LinearMap.ker
      (CriticalGK2.binaryEvaluation F (Matrix (Fin k) (Fin k) C) v).toLinearMap) :
    dualCoefficientSpace F n S ≤ LinearMap.ker (actualDualMatrixEvaluation F C k n v) := by
  rintro φ ⟨P, hP, rfl⟩
  change CriticalGK2.binaryEvaluation F (Matrix (Fin k) (Fin k) C) v
    (dualToAmbient F n (ambientToDual F n P)) = 0
  rw [dualToAmbient_ambientToDual F n P (hS hP)]
  exact hker hP

/-- The complete actual reset stage is killed by the whole matrix evaluation,
for arbitrary commutative coefficients and every letter assignment. -/
theorem actualResetSpace_le_matrix_kernel (C : Type*) [CommRing C] [Algebra F C]
    (n : ℕ) (t : CriticalGK2.StemWord n → F) (k : ℕ) (u : FreeMonoid Bool)
    (v : Bool → Matrix (Fin k) (Fin k) C) :
    actualStemBlockSpace F (CriticalGK2.localResetDegree n k u)
      (CriticalGK2.localResetCoefficients F n t k u) ≤
      LinearMap.ker (actualDualMatrixEvaluation F C k
        (CriticalGK2.localResetDegree n k u + 1) v) := by
  exact dualCoefficientSpace_le_matrix_kernel F C k _ v _
    (stemSpace_le_homogeneous F _ _)
    (resetSpace_le_matrix_kernel F C n t k u
      (CriticalGK2.binaryEvaluation F (Matrix (Fin k) (Fin k) C) v))

/-- Waiting's degree equation is unconditional arithmetic. -/
theorem actualWaitingSpace_degree (n : ℕ) :
    (n + 1) + (n + 1) = (2 * n + 1) + 1 := by omega

/-- Reset's degree equation is unconditional arithmetic. -/
theorem actualResetSpace_degree (n k : ℕ) (u : FreeMonoid Bool) :
    (((k * k + 1) * (k * k + 1) + u.length) + 1) * (n + 1) =
      CriticalGK2.localResetDegree n k u + 1 := by
  simp only [CriticalGK2.localResetDegree]
  ring

end

end CriticalGK2.Actual
