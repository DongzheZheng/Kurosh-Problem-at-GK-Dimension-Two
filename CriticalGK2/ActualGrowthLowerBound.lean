import CriticalGK2.NormalLanguageSurvival
import CriticalGK2.PositiveGradedSum

/-!
# The actual quadratic growth lower bound

The normal-word stream, the exclusion of periodic tails and the component
dimension lower bounds have already been supplied by the same actual sparse
nil algebra. Actual finite homogeneous independence then sums them inside
the actual degree filtration, giving a quadratic lower bound.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- Actual degree growth of the actual sparse positive quotient. -/
def sparseDegreeGrowth (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) (N : ℕ) : ℕ :=
  positiveDegreeGrowth F (sparseDualData F Λ hΛ)
    (sparseDualData_primalCoherent F Λ hΛ) N

/-- The fixed original-field algebra has this actual growth function. -/
def originalFieldDegreeGrowth (N : ℕ) : ℕ :=
  sparseDegreeGrowth F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges N

/-- The actual lower bound for every sparse construction, with the schedule
as its only ordinary numerical input. -/
theorem sparseDegreeGrowth_quadratic_lower (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (N : ℕ) :
    N * (N + 3) ≤ 2 * sparseDegreeGrowth F Λ hΛ N := by
  apply positiveDegreeGrowth_quadratic_lower_of_components F
    (sparseDualData F Λ hΛ) (sparseDualData_primalCoherent F Λ hΛ)
  intro m
  exact sparse_componentQuotient_finrank_lower F Λ hΛ (m + 1)

/-- A quadratic lower bound for the growth of the constructed algebra. -/
theorem originalFieldDegreeGrowth_quadratic_lower (N : ℕ) :
    N * (N + 3) ≤ 2 * originalFieldDegreeGrowth F N :=
  sparseDegreeGrowth_quadratic_lower F _ linearEnvelope_diverges N

/-- A weaker square form is convenient for the numerical GK endpoint. -/
theorem originalFieldDegreeGrowth_square_lower (N : ℕ) :
    N ^ 2 ≤ 2 * originalFieldDegreeGrowth F N := by
  have h : N ^ 2 ≤ N * (N + 3) := by
    rw [Nat.pow_two]
    exact Nat.mul_le_mul_left N (Nat.le_add_right N 3)
  exact h.trans (originalFieldDegreeGrowth_quadratic_lower F N)

#print axioms CriticalGK2.Actual.originalFieldDegreeGrowth_quadratic_lower
#print axioms CriticalGK2.Actual.originalFieldDegreeGrowth_square_lower

end

end CriticalGK2.Actual
