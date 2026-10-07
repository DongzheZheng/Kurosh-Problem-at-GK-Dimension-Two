import CriticalGK2.StageFiniteCutBudget
import CriticalGK2.SparseBudgetIndex

/-!
# The proved global budget of the actual sparse construction

The active finite stage is selected by the already-proved literal infinite
family. At the incoming endpoint of operation j, waiting still pays only
the old budget C_j. Earlier active stages pay C_(i+1), which is at most C_j.
This resolves every height without adding a global budget certificate.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

theorem actual_supportBudget_monotone (cost : ℕ → ℕ) : Monotone (supportBudget cost) := by
  apply monotone_nat_of_le_succ
  intro j
  have hp : 1 ≤ (2 : ℕ) ^ cost j :=
    Nat.succ_le_of_lt (pow_pos (by norm_num) _)
  change supportBudget cost j ≤ 2 ^ cost j * supportBudget cost j
  simpa only [one_mul] using Nat.mul_le_mul_right (supportBudget cost j) hp

/-- The global family up through the incoming waiting endpoint of stage j
has paid exactly the first j operation costs. The proof keeps all actual
intermediate block-power spaces supplied by the finite-stage constructor. -/
theorem constructedDualData_cutBound_before_start (waiting size : ℕ → ℕ)
    (j H : ℕ) (hH : H ≤ stageHeight F waiting size j + waiting j) :
    ActualDualCutBound F (2 ^ H) (constructedDualData F waiting size H)
      (supportBudget (fun i => operationSize (size i)) j) := by
  let i := activeStage F waiting size H
  let a := H - stageHeight F waiting size i
  have hlo := activeStage_lower F waiting size H
  have hhi := activeStage_upper F waiting size H
  change stageHeight F waiting size i ≤ H at hlo
  change H < stageHeight F waiting size (i + 1) at hhi
  have hd : stageHeight F waiting size i + a = H := by
    dsimp only [a]
    omega
  have ha : a ≤ waiting i + operationHeight (size i) := by
    have hs := stageHeight_succ F waiting size i
    omega
  have hup : H < stageHeight F waiting size (j + 1) := by
    rw [stageHeight_succ]
    have hp := operationHeight_pos (size j)
    omega
  have hij : i ≤ j := Nat.find_min' (exists_stage_end_above F waiting size H) hup
  have hinf := infiniteSpace_at_stage F waiting size i a ha
  rw [hd] at hinf
  change ActualDualCutBound F (2 ^ H)
    (dualCoefficientSpace F (2 ^ H) (infiniteSpace F waiting size H)) _
  rw [hinf]
  by_cases he : i = j
  · have haw : a ≤ waiting i := by
      have hj : H ≤ stageHeight F waiting size i + waiting i := by simpa only [he] using hH
      omega
    have h := stageSpace_waiting_cutBound_le_budget F waiting size i a haw
    rw [hd] at h
    have hc : supportBudget (fun t => operationSize (size t)) i ≤
        supportBudget (fun t => operationSize (size t)) j := by rw [he]
    exact actualDualCutBound_budget_mono F _ _ hc h
  · have hij1 : i + 1 ≤ j := by omega
    have h := stageSpace_cutBound_le_next_budget F waiting size i a ha
    rw [hd] at h
    exact actualDualCutBound_budget_mono F _ _
      (actual_supportBudget_monotone (fun t => operationSize (size t)) hij1) h

/-- Unconditional literal global support budget of the actual sparse family.
The only external input constructs its concrete schedule: an envelope tending
to infinity. Every support estimate is proved from actual polynomial spaces. -/
theorem sparseDualData_cutBound (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (j H : ℕ) (hH : H ≤ scheduledHeight Λ hΛ j) :
    ActualDualCutBound F (2 ^ H) (sparseDualData F Λ hΛ H)
      (supportBudget targetCost j) := by
  have hh : H ≤ stageHeight F (scheduledWaiting Λ hΛ) targetSize j +
      scheduledWaiting Λ hΛ j := by
    rw [scheduled_construction_alignment]
    exact hH
  exact constructedDualData_cutBound_before_start F (scheduledWaiting Λ hΛ) targetSize j H hh

#print axioms CriticalGK2.Actual.constructedDualData_cutBound_before_start
#print axioms CriticalGK2.Actual.sparseDualData_cutBound

end

end CriticalGK2.Actual
