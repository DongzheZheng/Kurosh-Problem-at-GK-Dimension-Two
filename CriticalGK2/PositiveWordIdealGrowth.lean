import CriticalGK2.PositiveWordIdealQuotient
import CriticalGK2.GenericGrowthTransfer

/-!
# Literal growth inside the positive further quotient

The degree filtration is a submodule of the actual augmentation kernel Q.
Its inclusion into B identifies it with the actual positive degree filtration
of H/I. Thus all bounds below concern finrank in the actual non-unital Q.
-/

namespace CriticalGK2.Actual

noncomputable section

open Filter
open scoped Topology

variable (F : Type*) [Field F]
variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)

theorem idealDegreeSpace_le_positive (n : ℕ) :
    idealDegreeSpace F I (n + 1) ≤
      (positiveWordIdealSubalgebra F I hpos).toSubmodule := by
  intro b hb
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.mp hb
  change wordIdealQuotientAugmentation F I hpos (wordIdealQuotientMap F I P) = 0
  rw [wordIdealQuotientAugmentation_map]
  exact augmentation_homogeneous_eq_zero F (n + 1) (by omega) P hP

theorem idealPositiveDegreeFiltration_le_positive (N : ℕ) :
    idealPositiveDegreeFiltration F I N ≤
      (positiveWordIdealSubalgebra F I hpos).toSubmodule := by
  unfold idealPositiveDegreeFiltration
  apply Finset.sup_le
  intro n _
  exact idealDegreeSpace_le_positive F I hpos n

def positiveIdealDegreeSpace (n : ℕ) :
    Submodule F (PositiveWordIdealQuotient F I hpos) :=
  (idealDegreeSpace F I (n + 1)).submoduleOf
    (positiveWordIdealSubalgebra F I hpos).toSubmodule

def positiveIdealDegreeFiltration (N : ℕ) :
    Submodule F (PositiveWordIdealQuotient F I hpos) :=
  (idealPositiveDegreeFiltration F I N).submoduleOf
    (positiveWordIdealSubalgebra F I hpos).toSubmodule

def positiveIdealDegreeFiltrationEquiv (N : ℕ) :
    positiveIdealDegreeFiltration F I hpos N ≃ₗ[F] idealPositiveDegreeFiltration F I N :=
  Submodule.submoduleOfEquivOfLe (idealPositiveDegreeFiltration_le_positive F I hpos N)

instance positiveIdealDegreeFiltration_finite (N : ℕ) :
    FiniteDimensional F (positiveIdealDegreeFiltration F I hpos N) :=
  FiniteDimensional.of_injective
    (positiveIdealDegreeFiltrationEquiv F I hpos N).toLinearMap
    (positiveIdealDegreeFiltrationEquiv F I hpos N).injective

def positiveIdealDegreeGrowth (N : ℕ) : ℕ :=
  Module.finrank F (positiveIdealDegreeFiltration F I hpos N)

theorem positiveIdealDegreeGrowth_eq (N : ℕ) :
    positiveIdealDegreeGrowth F I hpos N = idealPositiveDegreeGrowth F I N :=
  (positiveIdealDegreeFiltrationEquiv F I hpos N).finrank_eq

theorem positive_furtherQuotient_growth_quadratic_lower (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ)
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I)
    (hhom : WordIdealHomogeneous F I) (htail : NoWordTail F I) (N : ℕ) :
    N * (N + 3) ≤ 2 * positiveIdealDegreeGrowth F I hpos N := by
  rw [positiveIdealDegreeGrowth_eq]
  exact sparse_furtherQuotient_growth_quadratic_lower F Λ hΛ I hEI hhom htail N

theorem positive_furtherQuotient_envelope_upper (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (hmono : Monotone Λ)
    (hone : ∀ n : ℕ, 0 < n → 1 ≤ Λ n)
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I) (n : ℕ) (hn : 0 < n) :
    (positiveIdealDegreeGrowth F I hpos n : ℝ) ≤ 4 * ((n : ℝ) + 1) ^ 2 * Λ n := by
  rw [positiveIdealDegreeGrowth_eq]
  exact furtherQuotient_envelope_upper F Λ hΛ hmono hone I hEI n hn

theorem positive_furtherQuotient_logarithmic_limit (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ)
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I)
    (hhom : WordIdealHomogeneous F I) (htail : NoWordTail F I) :
    Tendsto (CriticalGK2.Growth.logarithmicGrowthRatio
      (positiveIdealDegreeGrowth F I hpos)) atTop (𝓝 2) := by
  have heq : positiveIdealDegreeGrowth F I hpos = idealPositiveDegreeGrowth F I := by
    funext n
    exact positiveIdealDegreeGrowth_eq F I hpos n
  rw [heq]
  exact furtherQuotient_logarithmic_limit F Λ hΛ I hEI hhom htail

#print axioms CriticalGK2.Actual.positiveIdealDegreeGrowth_eq
#print axioms CriticalGK2.Actual.positive_furtherQuotient_growth_quadratic_lower
#print axioms CriticalGK2.Actual.positive_furtherQuotient_envelope_upper
#print axioms CriticalGK2.Actual.positive_furtherQuotient_logarithmic_limit

end

end CriticalGK2.Actual
