import CriticalGK2.ActualBlockPowerCutBudget
import CriticalGK2.SparseSchedule

/-!
# Actual finite-stage support budgets

Waiting segments preserve the computed incoming common-stem budget exactly.
PI segments use the actual block-power spaces, paying their genuine 2^m
dimensions. The reset inclusion then bounds the computed outgoing common-stem
budget. All assertions concern actual coefficient-dual subspaces.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

theorem prefixState_blockPower_dyadicCutBound (P : PrefixState F) (a : ℕ) :
    ActualDualCutBound F (2 ^ (P.height + a))
      (dualCoefficientSpace F (2 ^ (P.height + a))
        (blockPower F (prefixSpace F P.polynomial) (2 ^ a)))
      (2 ^ (2 ^ a) * prefixStateCutBudget F P) := by
  have hd : 2 ^ a * 2 ^ P.height = (2 : ℕ) ^ (P.height + a) := by
    rw [pow_add]
    exact Nat.mul_comm _ _
  have h := actualDualCutBound_degreeCast F hd _ _
    (prefixState_blockPower_cutBound F P (2 ^ a))
  rwa [← dualCoefficientSpace_degreeCast F hd] at h

theorem resetPrefix_actualDualCutBound (P : PrefixState F) (k : ℕ) :
    ActualDualCutBound F (2 ^ (resetPrefix F P k).height)
      (dualCoefficientSpace F (2 ^ (resetPrefix F P k).height)
        (prefixSpace F (resetPrefix F P k).polynomial))
      (2 ^ operationSize k * prefixStateCutBudget F P) := by
  have h := prefixState_blockPower_dyadicCutBound F P (operationHeight k)
  change ActualDualCutBound F (2 ^ (P.height + operationHeight k))
    (dualCoefficientSpace F (2 ^ (P.height + operationHeight k))
      (blockPower F (prefixSpace F P.polynomial) (operationSize k)))
    (2 ^ operationSize k * prefixStateCutBudget F P) at h
  have hr := actualDualCutBound_mono F (2 ^ (P.height + operationHeight k))
    (Submodule.map_mono (resetPrefix_space_containment F P k)) _ h
  simpa only [resetPrefix_height] using hr

/-- The outgoing computed prefix budget is bounded using its actual all-cut
space, after proving the reset containment and block-power budget. -/
theorem resetPrefix_cutBudget_le (P : PrefixState F) (k : ℕ) :
    prefixStateCutBudget F (resetPrefix F P k) ≤
      2 ^ operationSize k * prefixStateCutBudget F P :=
  prefixStateCutBudget_le_of_cutBound F (resetPrefix F P k) _
    (resetPrefix_actualDualCutBound F P k)

theorem piSegment_actualDualCutBound (P : PrefixState F) (k a : ℕ)
    (ha : a ≤ operationHeight k) :
    ActualDualCutBound F (2 ^ (P.height + a))
      (dualCoefficientSpace F (2 ^ (P.height + a)) (piSegment F P k a))
      (2 ^ operationSize k * prefixStateCutBudget F P) := by
  by_cases he : a = operationHeight k
  · subst a
    simpa only [piSegment_endpoint, resetPrefix_height] using
      resetPrefix_actualDualCutBound F P k
  · rw [piSegment, if_neg he]
    have hm : 2 ^ a ≤ operationSize k :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) ha
    have hc : 2 ^ (2 ^ a) ≤ (2 : ℕ) ^ operationSize k :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hm
    exact actualDualCutBound_budget_mono F _ _
      (Nat.mul_le_mul_right (prefixStateCutBudget F P) hc)
      (prefixState_blockPower_dyadicCutBound F P a)

/-- Before the PI step begins, even its last incoming dyadic endpoint pays
only the unchanged old support budget. -/
theorem stageSpace_waiting_actualDualCutBound (P : PrefixState F) (k w a : ℕ)
    (ha : a ≤ w) :
    ActualDualCutBound F (2 ^ (P.height + a))
      (dualCoefficientSpace F (2 ^ (P.height + a)) (stageSpace F P k w a))
      (prefixStateCutBudget F P) := by
  have h := prefixState_actualDualCutBound F (waitIter F P a)
  rw [waitIter_height, waitIter_cutBudget] at h
  simpa only [stageSpace, if_pos ha] using h

theorem stageSpace_actualDualCutBound (P : PrefixState F) (k w a : ℕ)
    (ha : a ≤ w + operationHeight k) :
    ActualDualCutBound F (2 ^ (P.height + a))
      (dualCoefficientSpace F (2 ^ (P.height + a)) (stageSpace F P k w a))
      (2 ^ operationSize k * prefixStateCutBudget F P) := by
  by_cases haw : a ≤ w
  · have hp : 1 ≤ (2 : ℕ) ^ operationSize k :=
      Nat.succ_le_of_lt (pow_pos (by norm_num) _)
    apply actualDualCutBound_budget_mono F _ _ _
      (stageSpace_waiting_actualDualCutBound F P k w a haw)
    simpa only [one_mul] using Nat.mul_le_mul_right (prefixStateCutBudget F P) hp
  · have haop : a - w ≤ operationHeight k := by omega
    have hd : (waitIter F P w).height + (a - w) = P.height + a := by
      rw [waitIter_height]
      omega
    have h := piSegment_actualDualCutBound F (waitIter F P w) k (a - w) haop
    rw [hd, waitIter_cutBudget] at h
    simpa only [stageSpace, if_neg haw] using h

/-- The finite recursion discharges the entire prefix-state budget from the
actual polynomial constructors, for arbitrary waiting and size sequences. -/
theorem stagePrefix_cutBudget_le (waiting size : ℕ → ℕ) (j : ℕ) :
    prefixStateCutBudget F (stagePrefix F waiting size j) ≤
      supportBudget (fun i => operationSize (size i)) j := by
  induction j with
  | zero =>
      change prefixStateCutBudget F (initialPrefix F) ≤ 2
      exact le_of_eq (initialPrefix_cutBudget F)
  | succ j ih =>
      change prefixStateCutBudget F
        (resetPrefix F (waitIter F (stagePrefix F waiting size j) (waiting j)) (size j)) ≤
          2 ^ operationSize (size j) * supportBudget (fun i => operationSize (size i)) j
      have h := resetPrefix_cutBudget_le F
        (waitIter F (stagePrefix F waiting size j) (waiting j)) (size j)
      rw [waitIter_cutBudget] at h
      exact h.trans (Nat.mul_le_mul_left (2 ^ operationSize (size j)) ih)

theorem stageSpace_waiting_cutBound_le_budget (waiting size : ℕ → ℕ) (j a : ℕ)
    (ha : a ≤ waiting j) :
    ActualDualCutBound F (2 ^ (stageHeight F waiting size j + a))
      (dualCoefficientSpace F (2 ^ (stageHeight F waiting size j + a))
        (stageSpace F (stagePrefix F waiting size j) (size j) (waiting j) a))
      (supportBudget (fun i => operationSize (size i)) j) :=
  actualDualCutBound_budget_mono F _ _ (stagePrefix_cutBudget_le F waiting size j)
    (stageSpace_waiting_actualDualCutBound F (stagePrefix F waiting size j)
      (size j) (waiting j) a ha)

theorem stageSpace_cutBound_le_next_budget (waiting size : ℕ → ℕ) (j a : ℕ)
    (ha : a ≤ waiting j + operationHeight (size j)) :
    ActualDualCutBound F (2 ^ (stageHeight F waiting size j + a))
      (dualCoefficientSpace F (2 ^ (stageHeight F waiting size j + a))
        (stageSpace F (stagePrefix F waiting size j) (size j) (waiting j) a))
      (supportBudget (fun i => operationSize (size i)) (j + 1)) := by
  change ActualDualCutBound F _ _
    (2 ^ operationSize (size j) * supportBudget (fun i => operationSize (size i)) j)
  exact actualDualCutBound_budget_mono F _ _
    (Nat.mul_le_mul_left (2 ^ operationSize (size j))
      (stagePrefix_cutBudget_le F waiting size j))
    (stageSpace_actualDualCutBound F (stagePrefix F waiting size j)
      (size j) (waiting j) a ha)

#print axioms CriticalGK2.Actual.resetPrefix_cutBudget_le
#print axioms CriticalGK2.Actual.stagePrefix_cutBudget_le
#print axioms CriticalGK2.Actual.stageSpace_waiting_cutBound_le_budget
#print axioms CriticalGK2.Actual.stageSpace_cutBound_le_next_budget

end

end CriticalGK2.Actual
