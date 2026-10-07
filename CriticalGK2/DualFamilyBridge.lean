import CriticalGK2.DualDegreeBridge
import CriticalGK2.DyadicCoherence

/-!
# Actual homogeneous polynomial families produce genuine dyadic dual families

The input spaces are subspaces of the original actual free algebra. Only
homogeneity and actual multiplication containment are inputs. All actual dual
coherence, actual primal annihilator coherence, and nonvanishing of the dual
spaces are derived through the proved word-coefficient identification.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- Degreewise coefficient images of an actual dyadic homogeneous family. -/
def actualDualFamily (S : ℕ → Submodule F (WordAlgebra F)) : DyadicDualData F :=
  fun h => dualCoefficientSpace F (2 ^ h) (S h)

/-- Primal block coherence and homogeneity imply raw dual block coherence. -/
theorem actualDualFamily_dualCoherent (S : ℕ → Submodule F (WordAlgebra F))
    (hS : ∀ h, S h ≤ homogeneous F (2 ^ h))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h)) :
    DualCoherent F (actualDualFamily F S) := by
  apply (dualCoherent_iff_forward_inclusion F (actualDualFamily F S)).mpr
  intro h
  change dualCoefficientSpace F (2 ^ (h + 1)) (S (h + 1)) ≤
    (actualDualTensorProduct F (2 ^ h) (2 ^ h)
      (dualCoefficientSpace F (2 ^ h) (S h)) (dualCoefficientSpace F (2 ^ h) (S h))).map
      (homogeneousDualDegreeCast F (dyadicDoubleDegree h)).toLinearMap
  rw [dualCoefficientSpace_degreeCast F (dyadicDoubleDegree h)]
  apply Submodule.map_mono
  exact (Submodule.map_mono (hproduct h)).trans
    (dualCoefficientSpace_productSpan_le F (2 ^ h) (2 ^ h) (S h) (S h) (hS h) (hS h))

/-- Both actual primal annihilator coherence laws are consequently certified. -/
theorem actualDualFamily_primalCoherent (S : ℕ → Submodule F (WordAlgebra F))
    (hS : ∀ h, S h ≤ homogeneous F (2 ^ h))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h)) :
    PrimalCoherent F (actualDualFamily F S) :=
  dualCoherent_primalCoherent F _ (actualDualFamily_dualCoherent F S hS hproduct)

/-- A nonzero actual homogeneous component gives a nonzero actual dual
configuration, using the actual exact coefficient inverse. -/
theorem actualDualFamily_ne_bot (S : ℕ → Submodule F (WordAlgebra F))
    (hS : ∀ h, S h ≤ homogeneous F (2 ^ h)) (hne : ∀ h, S h ≠ ⊥) (h : ℕ) :
    actualDualFamily F S h ≠ ⊥ := by
  obtain ⟨P, hP, hPne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne h)
  intro hzero
  have hm : ambientToDual F (2 ^ h) P ∈ actualDualFamily F S h := ⟨P, hP, rfl⟩
  rw [hzero] at hm
  exact ambientToDual_ne_zero F (2 ^ h) P (hS h hP) hPne ((Submodule.mem_bot F).mp hm)

end

end CriticalGK2.Actual
