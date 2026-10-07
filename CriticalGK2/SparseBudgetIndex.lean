import CriticalGK2.SparseConstruction
import CriticalGK2.DyadicRoots

/-!
# The operation count appropriate to an actual root cut

Operation j first changes the space above scheduledHeight j. The number of
operations paid at a height H is therefore the least j with
H <= scheduledHeight j. This definition includes long waiting intervals and
the exact dyadic endpoints. All scheduling and root-size bounds below are
derived from the computed schedule.
-/

namespace CriticalGK2.Actual

noncomputable section

theorem target_supportBudget_monotone : Monotone (supportBudget targetCost) := by
  apply monotone_nat_of_le_succ
  intro j
  have hp : 1 ≤ (2 : ℕ) ^ targetCost j :=
    Nat.succ_le_iff.mpr (pow_pos (by omega) _)
  change supportBudget targetCost j ≤ 2 ^ targetCost j * supportBudget targetCost j
  simpa only [one_mul] using Nat.mul_le_mul_right (supportBudget targetCost j) hp

theorem scheduledHeight_index_le (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) (j : ℕ) :
    j ≤ scheduledHeight Λ hΛ j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
      have h := scheduledHeight_separated Λ hΛ j
      omega

theorem scheduledHeight_monotone (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) :
    Monotone (scheduledHeight Λ hΛ) :=
  (scaleHeight_strictMono targetCost targetDuration Λ hΛ).monotone

theorem exists_scheduledHeight_above (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) (H : ℕ) :
    ∃ j : ℕ, H ≤ scheduledHeight Λ hΛ j :=
  ⟨H, scheduledHeight_index_le Λ hΛ H⟩

/-- Operations already charged at the actual dyadic root height. -/
def begunOperationCount (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) (H : ℕ) : ℕ :=
  Nat.find (exists_scheduledHeight_above Λ hΛ H)

theorem begunOperationCount_upper (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) (H : ℕ) :
    H ≤ scheduledHeight Λ hΛ (begunOperationCount Λ hΛ H) :=
  Nat.find_spec (exists_scheduledHeight_above Λ hΛ H)

theorem begunOperationCount_minimal (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (H j : ℕ) (hj : j < begunOperationCount Λ hΛ H) :
    scheduledHeight Λ hΛ j < H :=
  Nat.lt_of_not_ge (Nat.find_min (exists_scheduledHeight_above Λ hΛ H) hj)

theorem begunOperationCount_mono (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) :
    Monotone (begunOperationCount Λ hΛ) := by
  intro H T hHT
  exact Nat.find_min' (exists_scheduledHeight_above Λ hΛ H)
    (hHT.trans (begunOperationCount_upper Λ hΛ T))

theorem begunOperationCount_gt_of_height (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (H j : ℕ) (hj : scheduledHeight Λ hΛ j < H) :
    j < begunOperationCount Λ hΛ H := by
  by_contra h
  have hle : begunOperationCount Λ hΛ H ≤ j := by omega
  have hh := scheduledHeight_monotone Λ hΛ hle
  have hu := begunOperationCount_upper Λ hΛ H
  omega

/-- The actual support budget to its actual paid-operation count is bounded
by the original degree. This uses the earlier scheduled height at j-1. -/
theorem root_operation_budget_power_le_degree (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (n : ℕ) (hn : 0 < n) :
    supportBudget targetCost (begunOperationCount Λ hΛ (strictDyadicRoot n)) ^
      begunOperationCount Λ hΛ (strictDyadicRoot n) ≤ n := by
  let j := begunOperationCount Λ hΛ (strictDyadicRoot n)
  change supportBudget targetCost j ^ j ≤ n
  by_cases hj : j = 0
  · simp only [hj, pow_zero]
    omega
  · have hpred : j - 1 < begunOperationCount Λ hΛ (strictDyadicRoot n) := by
      change j - 1 < j
      omega
    have hheight := begunOperationCount_minimal Λ hΛ (strictDyadicRoot n) (j - 1) hpred
    have he : j - 1 + 1 = j := by omega
    have hcost := scaleHeight_budget_pow targetCost targetDuration Λ hΛ (j - 1)
    change supportBudget targetCost (j - 1 + 1) ^ (j - 1 + 1) ≤
      2 ^ scheduledHeight Λ hΛ (j - 1) at hcost
    rw [he] at hcost
    have hh : scheduledHeight Λ hΛ (j - 1) ≤ Nat.log 2 n := by
      dsimp only [strictDyadicRoot] at hheight
      omega
    exact hcost.trans ((Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hh).trans
      (Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)))

/-- Every fixed operation count has an explicit eventual degree threshold. -/
theorem root_operation_count_ge_after_threshold (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (J n : ℕ) (hJ : 0 < J)
    (hn : 2 ^ scheduledHeight Λ hΛ (J - 1) ≤ n) :
    J ≤ begunOperationCount Λ hΛ (strictDyadicRoot n) := by
  have hroot := strictDyadicRoot_monotone hn
  rw [strictDyadicRoot_two_pow] at hroot
  have hj : scheduledHeight Λ hΛ (J - 1) < strictDyadicRoot n := by omega
  have hcount := begunOperationCount_gt_of_height Λ hΛ (strictDyadicRoot n) (J - 1) hj
  omega

#print axioms CriticalGK2.Actual.root_operation_budget_power_le_degree
#print axioms CriticalGK2.Actual.root_operation_count_ge_after_threshold

end

end CriticalGK2.Actual
