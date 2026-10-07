import Mathlib

/-!
# Sparse scheduling on actual integer scales

This module proves the existence of all scale choices, from divergence of the
given real envelope and arbitrary finite operation costs.
Stages are numbered from zero; stage `j` corresponds to manuscript stage `j+1`.
-/

namespace CriticalGK2

/-- The exact eventual lower-bound meaning of a real envelope tending to infinity. -/
def EnvelopeDiverges (Λ : ℕ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M ≤ Λ n

/-- The support budget before the first operation is two. -/
def supportBudget (κ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 2
  | j + 1 => 2 ^ κ j * supportBudget κ j

theorem supportBudget_pos (κ : ℕ → ℕ) (j : ℕ) :
    0 < supportBudget κ j := by
  induction j with
  | zero => norm_num [supportBudget]
  | succ j ih =>
      exact Nat.mul_pos (pow_pos (by norm_num) _) ih

/-- A convenient intentionally loose scale bound, proved without evaluating huge powers. -/
theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hp : 0 < (2 : ℕ) ^ n := pow_pos (by norm_num) _
      rw [pow_succ]
      omega

/-- All three scale constraints can be paid at once. -/
theorem exists_next_scale (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (C prev duration j : ℕ) :
    ∃ h : ℕ, prev + duration < h ∧
      C ^ (j + 1) ≤ 2 ^ h ∧ (C : ℝ) ^ 2 ≤ Λ (2 ^ h) := by
  obtain ⟨N, hN⟩ := hΛ ((C : ℝ) ^ 2)
  let h := prev + duration + C ^ (j + 1) + N + 1
  refine ⟨h, ?_, ?_, ?_⟩
  · dsimp [h]
    omega
  · have hC : C ^ (j + 1) ≤ h := by dsimp [h]; omega
    exact hC.trans (nat_le_two_pow h)
  · apply hN
    have hn : N ≤ h := by dsimp [h]; omega
    exact hn.trans (nat_le_two_pow h)

noncomputable def nextScale (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (C prev duration j : ℕ) : ℕ :=
  Classical.choose (exists_next_scale Λ hΛ C prev duration j)

theorem nextScale_spec (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (C prev duration j : ℕ) :
    prev + duration < nextScale Λ hΛ C prev duration j ∧
    C ^ (j + 1) ≤ 2 ^ nextScale Λ hΛ C prev duration j ∧
    (C : ℝ) ^ 2 ≤ Λ (2 ^ nextScale Λ hΛ C prev duration j) :=
  Classical.choose_spec (exists_next_scale Λ hΛ C prev duration j)

/-- Recursive heights use the previously completed layer as their next lower bound. -/
noncomputable def scaleHeight (κ duration : ℕ → ℕ)
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) : ℕ → ℕ
  | 0 => nextScale Λ hΛ (supportBudget κ 1) 0 0 0
  | j + 1 => nextScale Λ hΛ (supportBudget κ (j + 2))
      (scaleHeight κ duration Λ hΛ j) (duration j) (j + 1)

theorem scaleHeight_separated (κ duration : ℕ → ℕ)
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) (j : ℕ) :
    scaleHeight κ duration Λ hΛ j + duration j <
      scaleHeight κ duration Λ hΛ (j + 1) := by
  exact (nextScale_spec Λ hΛ (supportBudget κ (j + 2))
    (scaleHeight κ duration Λ hΛ j) (duration j) (j + 1)).1

theorem scaleHeight_budget_pow (κ duration : ℕ → ℕ)
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) (j : ℕ) :
    supportBudget κ (j + 1) ^ (j + 1) ≤
      2 ^ scaleHeight κ duration Λ hΛ j := by
  cases j with
  | zero => exact (nextScale_spec Λ hΛ (supportBudget κ 1) 0 0 0).2.1
  | succ j =>
      exact (nextScale_spec Λ hΛ (supportBudget κ (j + 2))
        (scaleHeight κ duration Λ hΛ j) (duration j) (j + 1)).2.1

theorem scaleHeight_envelope (κ duration : ℕ → ℕ)
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) (j : ℕ) :
    (supportBudget κ (j + 1) : ℝ) ^ 2 ≤
      Λ (2 ^ scaleHeight κ duration Λ hΛ j) := by
  cases j with
  | zero => exact (nextScale_spec Λ hΛ (supportBudget κ 1) 0 0 0).2.2
  | succ j =>
      exact (nextScale_spec Λ hΛ (supportBudget κ (j + 2))
        (scaleHeight κ duration Λ hΛ j) (duration j) (j + 1)).2.2

theorem scaleHeight_strictMono (κ duration : ℕ → ℕ)
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) :
    StrictMono (scaleHeight κ duration Λ hΛ) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hs := scaleHeight_separated κ duration Λ hΛ j
  omega

/-- The formal scheduling statement keeps all operation costs arbitrary and finite. -/
theorem exists_sparse_schedule (κ duration : ℕ → ℕ)
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) :
    ∃ h : ℕ → ℕ, StrictMono h ∧
      (∀ j, h j + duration j < h (j + 1)) ∧
      (∀ j, supportBudget κ (j + 1) ^ (j + 1) ≤ 2 ^ h j) ∧
      (∀ j, (supportBudget κ (j + 1) : ℝ) ^ 2 ≤ Λ (2 ^ h j)) := by
  exact ⟨scaleHeight κ duration Λ hΛ,
    scaleHeight_strictMono κ duration Λ hΛ,
    scaleHeight_separated κ duration Λ hΛ,
    scaleHeight_budget_pow κ duration Λ hΛ,
    scaleHeight_envelope κ duration Λ hΛ⟩

end CriticalGK2
