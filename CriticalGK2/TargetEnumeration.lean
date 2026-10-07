import CriticalGK2.AutomatonFiniteEvaluation

/-! Exact countable enumeration of every positive matrix-size/degree pair. -/

namespace CriticalGK2.Actual

noncomputable section

def targetRank (j : ℕ) : ℕ := (Nat.unpair j).1 + 1
def targetDegree (j : ℕ) : ℕ := (Nat.unpair j).2 + 1
def targetSize (j : ℕ) : ℕ :=
  CriticalGK2.Automaton.stateNumber (targetRank j) (targetDegree j)

theorem targetRank_pos (j : ℕ) : 0 < targetRank j := Nat.succ_pos _
theorem targetDegree_pos (j : ℕ) : 0 < targetDegree j := Nat.succ_pos _

theorem target_pair_covered (r d : ℕ) (hr : 0 < r) (hd : 0 < d) :
    ∃ j : ℕ, targetRank j = r ∧ targetDegree j = d ∧
      targetSize j = CriticalGK2.Automaton.stateNumber r d := by
  refine ⟨Nat.pair (r - 1) (d - 1), ?_, ?_, ?_⟩
  · simp only [targetRank, Nat.unpair_pair]
    omega
  · simp only [targetDegree, Nat.unpair_pair]
    omega
  · have h1 : targetRank (Nat.pair (r - 1) (d - 1)) = r := by
      simp only [targetRank, Nat.unpair_pair]; omega
    have h2 : targetDegree (Nat.pair (r - 1) (d - 1)) = d := by
      simp only [targetDegree, Nat.unpair_pair]; omega
    rw [targetSize, h1, h2]

end

end CriticalGK2.Actual
