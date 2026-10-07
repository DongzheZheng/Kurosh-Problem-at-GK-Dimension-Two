import CriticalGK2.ConcreteConstruction
import CriticalGK2.TargetEnumeration
import CriticalGK2.SparseSchedule

/-!
# A concrete sparse infinite construction covering all finite automata

The waiting counts are computed from the sparse schedule. The construction
establishes alignment, coherence and survival. Its envelope bounds control
the finite operation budget, which gives the algebra's growth estimates
through the cut-support lemmas.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

def targetCost (j : ℕ) : ℕ := operationSize (targetSize j)
def targetDuration (j : ℕ) : ℕ := operationHeight (targetSize j)

def scheduledHeight (Λ : ℕ → ℝ) (hΛ : CriticalGK2.EnvelopeDiverges Λ) : ℕ → ℕ :=
  CriticalGK2.scaleHeight targetCost targetDuration Λ hΛ

def scheduledWaiting (Λ : ℕ → ℝ) (hΛ : CriticalGK2.EnvelopeDiverges Λ) : ℕ → ℕ
  | 0 => scheduledHeight Λ hΛ 0
  | j + 1 => scheduledHeight Λ hΛ (j + 1) -
      (scheduledHeight Λ hΛ j + targetDuration j)

theorem scheduledHeight_separated (Λ : ℕ → ℝ) (hΛ : CriticalGK2.EnvelopeDiverges Λ)
    (j : ℕ) :
    scheduledHeight Λ hΛ j + targetDuration j < scheduledHeight Λ hΛ (j + 1) :=
  CriticalGK2.scaleHeight_separated _ _ _ _ _

/-- The actual incoming prefix has reached exactly the scheduled start
height after the concrete waiting operations. -/
theorem scheduled_construction_alignment (Λ : ℕ → ℝ)
    (hΛ : CriticalGK2.EnvelopeDiverges Λ) (j : ℕ) :
    stageHeight F (scheduledWaiting Λ hΛ) targetSize j + scheduledWaiting Λ hΛ j =
      scheduledHeight Λ hΛ j := by
  induction j with
  | zero => simp [scheduledWaiting]
  | succ j ih =>
    rw [stageHeight_succ, ih]
    change scheduledHeight Λ hΛ j + targetDuration j +
      (scheduledHeight Λ hΛ (j + 1) -
        (scheduledHeight Λ hΛ j + targetDuration j)) = scheduledHeight Λ hΛ (j + 1)
    have hs := scheduledHeight_separated Λ hΛ j
    omega

theorem scheduled_construction_endpoint (Λ : ℕ → ℝ)
    (hΛ : CriticalGK2.EnvelopeDiverges Λ) (j : ℕ) :
    stageHeight F (scheduledWaiting Λ hΛ) targetSize (j + 1) =
      scheduledHeight Λ hΛ j + targetDuration j := by
  rw [stageHeight_succ, scheduled_construction_alignment]
  rfl

def sparseDualData (Λ : ℕ → ℝ) (hΛ : CriticalGK2.EnvelopeDiverges Λ) : DyadicDualData F :=
  constructedDualData F (scheduledWaiting Λ hΛ) targetSize

theorem sparseDualData_primalCoherent (Λ : ℕ → ℝ) (hΛ : CriticalGK2.EnvelopeDiverges Λ) :
    PrimalCoherent F (sparseDualData F Λ hΛ) :=
  constructedPrimalCoherent F _ _

theorem sparseDualData_ne_bot (Λ : ℕ → ℝ) (hΛ : CriticalGK2.EnvelopeDiverges Λ) (h : ℕ) :
    sparseDualData F Λ hΛ h ≠ ⊥ :=
  constructedDualData_ne_bot F _ _ _

theorem sparse_operation_budget (Λ : ℕ → ℝ) (hΛ : CriticalGK2.EnvelopeDiverges Λ)
    (j : ℕ) :
    (CriticalGK2.supportBudget targetCost (j + 1) : ℝ) ^ 2 ≤
      Λ (2 ^ scheduledHeight Λ hΛ j) :=
  CriticalGK2.scaleHeight_envelope _ _ _ _ _

/-- Every positive matrix-size and word-degree pair receives a concrete,
nonzero, universal matrix-PI endpoint in the same actual infinite family. -/
theorem sparse_all_automata_endpoint (Λ : ℕ → ℝ) (hΛ : CriticalGK2.EnvelopeDiverges Λ)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d) :
    ∃ H : ℕ, ∀ (C : Type*) [CommRing C] [Algebra F C]
      (v : Bool → Matrix (Fin (CriticalGK2.Automaton.stateNumber r d))
        (Fin (CriticalGK2.Automaton.stateNumber r d)) C),
      sparseDualData F Λ hΛ H ≤ LinearMap.ker
        (actualDualMatrixEvaluation F C (CriticalGK2.Automaton.stateNumber r d) (2 ^ H) v) := by
  obtain ⟨j, _, _, hj⟩ := target_pair_covered r d hr hd
  refine ⟨stageHeight F (scheduledWaiting Λ hΛ) targetSize (j + 1), ?_⟩
  intro C _ _ v
  have h := constructed_dual_endpoint_killed F (scheduledWaiting Λ hΛ) targetSize C j
  rw [hj] at h
  exact h v

#print axioms CriticalGK2.Actual.scheduled_construction_alignment
#print axioms CriticalGK2.Actual.sparseDualData_primalCoherent
#print axioms CriticalGK2.Actual.sparse_all_automata_endpoint

end

end CriticalGK2.Actual
