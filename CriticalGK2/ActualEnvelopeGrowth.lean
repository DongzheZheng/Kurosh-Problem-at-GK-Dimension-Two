import CriticalGK2.ActualGrowthFromCutBudget

/-!
# The prescribed growth envelope at every positive integer

The schedule's paid-operation count is the same count used in the actual
completion bound. When the count is positive, the preceding scheduled height
is no larger than log_2(n); monotonicity of the prescribed envelope then reads
the actual paid budget at n. The initial count has the literal budget two.

The infinite-family cut inequality gives the prescribed envelope estimate.
For the sparse construction, this inequality is proved by the cut-budget
lemmas.
-/

namespace CriticalGK2.Actual

noncomputable section

theorem root_supportBudget_square_le_envelope (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (hmono : Monotone Λ)
    (hone : ∀ n : ℕ, 0 < n → 1 ≤ Λ n) (n : ℕ) (hn : 0 < n) :
    (supportBudget targetCost (begunOperationCount Λ hΛ (strictDyadicRoot n)) : ℝ) ^ 2
      ≤ 4 * Λ n := by
  let j := begunOperationCount Λ hΛ (strictDyadicRoot n)
  change (supportBudget targetCost j : ℝ) ^ 2 ≤ 4 * Λ n
  by_cases hj : j = 0
  · rw [hj]
    change (2 : ℝ) ^ (2 : ℕ) ≤ 4 * Λ n
    nlinarith [hone n hn]
  · have hpred : j - 1 < begunOperationCount Λ hΛ (strictDyadicRoot n) := by
      change j - 1 < j
      omega
    have hheight := begunOperationCount_minimal Λ hΛ (strictDyadicRoot n) (j - 1) hpred
    have he : j - 1 + 1 = j := by omega
    have hc := sparse_operation_budget Λ hΛ (j - 1)
    rw [he] at hc
    have hh : scheduledHeight Λ hΛ (j - 1) ≤ Nat.log 2 n := by
      dsimp only [strictDyadicRoot] at hheight
      omega
    have hs : 2 ^ scheduledHeight Λ hΛ (j - 1) ≤ n :=
      (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hh).trans
        (Nat.pow_log_le_self 2 (Nat.ne_of_gt hn))
    have hb : (supportBudget targetCost j : ℝ) ^ 2 ≤ Λ n := hc.trans (hmono hs)
    have hpos : 0 ≤ Λ n := (by norm_num : (0 : ℝ) ≤ 1).trans (hone n hn)
    linarith

variable (F : Type*) [Field F]

theorem sparseDegreeGrowth_envelope_upper_of_cutBounds (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (hmono : Monotone Λ)
    (hone : ∀ n : ℕ, 0 < n → 1 ≤ Λ n)
    (hbudget : ∀ j H : ℕ, H ≤ scheduledHeight Λ hΛ j →
      ActualDualCutBound F (2 ^ H) (sparseDualData F Λ hΛ H)
        (supportBudget targetCost j)) (n : ℕ) (hn : 0 < n) :
    (sparseDegreeGrowth F Λ hΛ n : ℝ) ≤ 4 * ((n : ℝ) + 1) ^ 2 * Λ n := by
  have hg : (sparseDegreeGrowth F Λ hΛ n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) *
      (supportBudget targetCost (begunOperationCount Λ hΛ (strictDyadicRoot n)) : ℝ) ^ 2 := by
    exact_mod_cast sparseDegreeGrowth_le_scheduled_budget_of_cutBounds F Λ hΛ hbudget n hn
  have hc := root_supportBudget_square_le_envelope Λ hΛ hmono hone n hn
  have hpos : 0 ≤ Λ n := (by norm_num : (0 : ℝ) ≤ 1).trans (hone n hn)
  calc
    (sparseDegreeGrowth F Λ hΛ n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) *
        (supportBudget targetCost (begunOperationCount Λ hΛ (strictDyadicRoot n)) : ℝ) ^ 2 := hg
    _ ≤ (n : ℝ) * ((n : ℝ) + 1) * (4 * Λ n) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 4 * ((n : ℝ) * ((n : ℝ) + 1)) * Λ n := by ring
    _ ≤ 4 * ((n : ℝ) + 1) ^ 2 * Λ n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
          (by norm_num)) hpos

#print axioms CriticalGK2.Actual.root_supportBudget_square_le_envelope
#print axioms CriticalGK2.Actual.sparseDegreeGrowth_envelope_upper_of_cutBounds

end

end CriticalGK2.Actual
