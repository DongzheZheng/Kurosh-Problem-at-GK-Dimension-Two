import CriticalGK2.ConstructedGrowthEndpoint
import CriticalGK2.LogarithmicGrowth

namespace CriticalGK2.Actual

open Filter
open scoped Topology

noncomputable section

variable (F : Type*) [Field F]

theorem sparseDegreeGrowth_logarithmic_limit (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) :
    Tendsto (CriticalGK2.Growth.logarithmicGrowthRatio (sparseDegreeGrowth F Λ hΛ))
      atTop (𝓝 2) := by
  apply CriticalGK2.Growth.tendsto_logarithmicGrowthRatio_two
  · intro n _
    have h := sparseDegreeGrowth_quadratic_lower F Λ hΛ n
    have hs : n ^ 2 ≤ n * (n + 3) := by
      rw [Nat.pow_two]
      exact Nat.mul_le_mul_left n (Nat.le_add_right n 3)
    exact_mod_cast hs.trans h
  · exact sparseDegreeGrowth_near_two_upper F Λ hΛ

theorem sparseDegreeGrowth_logarithmic_limsup (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) :
    Filter.limsup (CriticalGK2.Growth.logarithmicGrowthRatio (sparseDegreeGrowth F Λ hΛ))
      atTop = 2 :=
  (sparseDegreeGrowth_logarithmic_limit F Λ hΛ).limsup_eq

theorem originalFieldDegreeGrowth_logarithmic_limsup :
    Filter.limsup (CriticalGK2.Growth.logarithmicGrowthRatio (originalFieldDegreeGrowth F))
      atTop = 2 :=
  sparseDegreeGrowth_logarithmic_limsup F _ linearEnvelope_diverges

#print axioms CriticalGK2.Actual.sparseDegreeGrowth_logarithmic_limsup
#print axioms CriticalGK2.Actual.originalFieldDegreeGrowth_logarithmic_limsup

end

end CriticalGK2.Actual
