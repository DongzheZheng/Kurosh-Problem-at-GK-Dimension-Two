import CriticalGK2.ActualSpaceCutBudget
import CriticalGK2.ActualGrowthLowerBound
import CriticalGK2.PositiveWordFiltration
import CriticalGK2.ScheduledGrowthUpper

/-!
# From literal infinite-family cut bounds to actual word growth

The only construction-specific input here is a literal all-cut inequality
for the actual infinite dual family. This module reads it through the actual
completion annihilators, including their zero-degree endpoints, and sums
the actual positive homogeneous quotient dimensions. The output is the
growth exponent of the actual two-generator word filtration.

The actual global cut inequality is to be discharged by the stage-budget
module. Until that theorem is supplied, the lemmas in this file remain
conditional and are named accordingly.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

theorem homogeneousDual_zero_finrank :
    Module.finrank F (HomogeneousDual F 0) = 1 := by
  rw [← (coefficientSelfDual F 0).finrank_eq, finrank_homogeneous_zero]

theorem zeroDegree_dualSubmodule_finrank_le_one
    (S : Submodule F (HomogeneousDual F 0)) : Module.finrank F S ≤ 1 := by
  classical
  letI : FiniteDimensional F (HomogeneousDual F 0) :=
    (homogeneousWordBasis F 0).dualBasis.finiteDimensional_of_finite
  calc
    Module.finrank F S ≤ Module.finrank F (HomogeneousDual F 0) := by
      simpa only [finrank_top] using Submodule.finrank_mono (show S ≤ ⊤ from le_top)
    _ = 1 := homogeneousDual_zero_finrank F

theorem sparseDegreeGrowth_le_scheduled_budget_of_cutBounds (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ)
    (hbudget : ∀ j H : ℕ, H ≤ scheduledHeight Λ hΛ j →
      ActualDualCutBound F (2 ^ H) (sparseDualData F Λ hΛ H)
        (supportBudget targetCost j))
    (N : ℕ) (hN : 0 < N) :
    sparseDegreeGrowth F Λ hΛ N ≤ N * (N + 1) *
      supportBudget targetCost (begunOperationCount Λ hΛ (strictDyadicRoot N)) ^ 2 := by
  let j : ℕ := begunOperationCount Λ hΛ (strictDyadicRoot N)
  let B : ℕ := supportBudget targetCost j
  have hBpos : 1 ≤ B := Nat.succ_le_of_lt (supportBudget_pos targetCost j)
  have hh : ∀ n : ℕ, n ≤ N →
      ActualDualCutBound F (2 ^ strictDyadicRoot n)
        (sparseDualData F Λ hΛ (strictDyadicRoot n)) B := by
    intro n hn
    exact hbudget j _ ((strictDyadicRoot_monotone hn).trans
      (begunOperationCount_upper Λ hΛ (strictDyadicRoot N)))
  have hl : ∀ n : ℕ, n ≤ N →
      Module.finrank F ((homogeneousLeftCompletion F (sparseDualData F Λ hΛ) n).dualAnnihilator)
        ≤ B := by
    intro n hn
    by_cases hz : n = 0
    · subst n
      exact (zeroDegree_dualSubmodule_finrank_le_one F _).trans hBpos
    · exact leftCompletion_finrank_le_of_rootCutBound F _ n B hz (hh n hn)
  have hr : ∀ n : ℕ, n ≤ N →
      Module.finrank F ((homogeneousRightCompletion F (sparseDualData F Λ hΛ) n).dualAnnihilator)
        ≤ B := by
    intro n hn
    by_cases hz : n = 0
    · subst n
      exact (zeroDegree_dualSubmodule_finrank_le_one F _).trans hBpos
    · exact rightCompletion_finrank_le_of_rootCutBound F _ n B hz (hh n hn)
  change positiveDegreeGrowth F _ _ N ≤ N * (N + 1) * B ^ 2
  apply positiveDegreeGrowth_le_uniform_cut_budget
  · intro m hm i
    have hm' := Finset.mem_range.mp hm
    have hi := i.isLt
    exact hl i.val (by omega)
  · intro m hm i
    have hm' := Finset.mem_range.mp hm
    exact hr (m + 1 - i.val) (by omega)

theorem sparseDegreeGrowth_near_two_upper_of_cutBounds (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ)
    (hbudget : ∀ j H : ℕ, H ≤ scheduledHeight Λ hΛ j →
      ActualDualCutBound F (2 ^ H) (sparseDualData F Λ hΛ H)
        (supportBudget targetCost j)) (ε : ℝ) (hε : 0 < ε) :
    2 + ε ∈ CriticalGK2.Growth.UpperExponentSet (sparseDegreeGrowth F Λ hΛ) := by
  apply CriticalGK2.Growth.near_two_upper_of_scheduled_budget Λ hΛ
  · exact positiveDegreeGrowth_mono F _ _
  · exact sparseDegreeGrowth_le_scheduled_budget_of_cutBounds F Λ hΛ hbudget
  · exact hε

theorem sparseDegreeGrowth_gkExponent_eq_two_of_cutBounds (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ)
    (hbudget : ∀ j H : ℕ, H ≤ scheduledHeight Λ hΛ j →
      ActualDualCutBound F (2 ^ H) (sparseDualData F Λ hΛ H)
        (supportBudget targetCost j)) :
    CriticalGK2.Growth.GKExponent (sparseDegreeGrowth F Λ hΛ) = 2 := by
  apply CriticalGK2.Growth.gkExponent_eq_two_of_quadratic_lower_near_two_upper
  · intro n _hn
    have h := sparseDegreeGrowth_quadratic_lower F Λ hΛ n
    have hs : n ^ 2 ≤ n * (n + 3) := by
      rw [Nat.pow_two]
      exact Nat.mul_le_mul_left n (Nat.le_add_right n 3)
    exact_mod_cast hs.trans h
  · exact sparseDegreeGrowth_near_two_upper_of_cutBounds F Λ hΛ hbudget

#print axioms CriticalGK2.Actual.sparseDegreeGrowth_le_scheduled_budget_of_cutBounds
#print axioms CriticalGK2.Actual.sparseDegreeGrowth_gkExponent_eq_two_of_cutBounds

end

end CriticalGK2.Actual
