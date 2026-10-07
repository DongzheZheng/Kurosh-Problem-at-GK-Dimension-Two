import CriticalGK2.ActualPositiveUnitization

/-! The actual standard unital word-growth function is one plus the actual
positive growth function. The proved bounds give its logarithmic limit two. -/

namespace CriticalGK2.Actual

noncomputable section

open Filter
open scoped Topology

variable (F : Type*) [Field F]
variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)

theorem positiveUnitizationGrowth_quadratic_lower (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ)
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I)
    (hhom : WordIdealHomogeneous F I) (htail : NoWordTail F I)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ 2 ≤ 2 * (positiveUnitizationDegreeGrowth F I hpos n : ℝ) := by
  have hl := positive_furtherQuotient_growth_quadratic_lower F I hpos Λ hΛ hEI hhom htail n
  have hs : n ^ 2 ≤ n * (n + 3) := by
    rw [Nat.pow_two]
    exact Nat.mul_le_mul_left n (Nat.le_add_right n 3)
  have hu : positiveIdealDegreeGrowth F I hpos n ≤ positiveUnitizationDegreeGrowth F I hpos n := by
    rw [positiveUnitizationDegreeGrowth_eq]
    omega
  exact_mod_cast (hs.trans hl).trans (Nat.mul_le_mul_left 2 hu)

theorem positiveUnitizationGrowth_upper_exponents (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ)
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I)
    (hhom : WordIdealHomogeneous F I) (htail : NoWordTail F I)
    (ε : ℝ) (hε : 0 < ε) :
    2 + ε ∈ CriticalGK2.Growth.UpperExponentSet (positiveUnitizationDegreeGrowth F I hpos) := by
  obtain ⟨C, hC, hupper⟩ := furtherQuotient_upper_exponents F Λ hΛ I hEI ε hε
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro n hn
  have hl := positive_furtherQuotient_growth_quadratic_lower F I hpos Λ hΛ hEI hhom htail n
  have hpositive : 1 ≤ positiveIdealDegreeGrowth F I hpos n := by
    by_contra h
    have hz : positiveIdealDegreeGrowth F I hpos n = 0 := by omega
    rw [hz] at hl
    nlinarith
  have htwo : positiveUnitizationDegreeGrowth F I hpos n ≤
      2 * positiveIdealDegreeGrowth F I hpos n := by
    rw [positiveUnitizationDegreeGrowth_eq]
    omega
  have hu := hupper n hn
  rw [← positiveIdealDegreeGrowth_eq F I hpos n] at hu
  have ht : (positiveUnitizationDegreeGrowth F I hpos n : ℝ) ≤
      2 * (positiveIdealDegreeGrowth F I hpos n : ℝ) := by exact_mod_cast htwo
  calc
    _ ≤ 2 * (positiveIdealDegreeGrowth F I hpos n : ℝ) := ht
    _ ≤ 2 * (C * (n : ℝ) ^ (2 + ε)) := mul_le_mul_of_nonneg_left hu (by norm_num)
    _ = (2 * C) * (n : ℝ) ^ (2 + ε) := by ring

theorem positiveUnitizationGrowth_logarithmic_limit (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ)
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I)
    (hhom : WordIdealHomogeneous F I) (htail : NoWordTail F I) :
    Tendsto (CriticalGK2.Growth.logarithmicGrowthRatio
      (positiveUnitizationDegreeGrowth F I hpos)) atTop (𝓝 2) :=
  CriticalGK2.Growth.tendsto_logarithmicGrowthRatio_two
    (positiveUnitizationDegreeGrowth F I hpos)
    (positiveUnitizationGrowth_quadratic_lower F I hpos Λ hΛ hEI hhom htail)
    (positiveUnitizationGrowth_upper_exponents F I hpos Λ hΛ hEI hhom htail)

theorem positiveUnitizationGrowth_logarithmic_limsup (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ)
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I)
    (hhom : WordIdealHomogeneous F I) (htail : NoWordTail F I) :
    Filter.limsup (CriticalGK2.Growth.logarithmicGrowthRatio
      (positiveUnitizationDegreeGrowth F I hpos)) atTop = 2 :=
  (positiveUnitizationGrowth_logarithmic_limit F I hpos Λ hΛ hEI hhom htail).limsup_eq

#print axioms CriticalGK2.Actual.positiveUnitizationGrowth_logarithmic_limit
#print axioms CriticalGK2.Actual.positiveUnitizationGrowth_logarithmic_limsup

end

end CriticalGK2.Actual
