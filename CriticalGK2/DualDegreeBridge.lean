import CriticalGK2.DualWordBridge
import CriticalGK2.DyadicDegreeCast

/-! # Exact degree transport for actual coefficient-dual spaces -/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

@[simp]
theorem ambientToDual_degreeCast {a b : ℕ} (hab : a = b) (P : WordAlgebra F) :
    homogeneousDualDegreeCast F hab (ambientToDual F a P) = ambientToDual F b P := by
  subst b
  rfl

@[simp]
theorem dualToAmbient_degreeCast {a b : ℕ} (hab : a = b) (φ : HomogeneousDual F a) :
    dualToAmbient F b (homogeneousDualDegreeCast F hab φ) = dualToAmbient F a φ := by
  subst b
  rfl

/-- Coefficient-space degree transport is exactly the proved homogeneous-dual cast. -/
theorem dualCoefficientSpace_degreeCast {a b : ℕ} (hab : a = b)
    (S : Submodule F (WordAlgebra F)) :
    dualCoefficientSpace F b S =
      (dualCoefficientSpace F a S).map (homogeneousDualDegreeCast F hab).toLinearMap := by
  subst b
  simp [homogeneousDualDegreeCast]

end

end CriticalGK2.Actual
