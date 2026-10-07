import Mathlib
import CriticalGK2.ActualWordSpaces

/-!
# Exact dyadic endpoints used by the actual all-cut construction

All statements concern `Actual.strictDyadicRoot`, the same function appearing
in the raw definitions of the actual left and right completion submodules.
-/

namespace CriticalGK2.Actual

theorem strictDyadicRoot_pos (n : ℕ) : 0 < strictDyadicRoot n := by
  simp [strictDyadicRoot]

theorem lt_strictDyadicRoot_pow (n : ℕ) : n < 2 ^ strictDyadicRoot n := by
  exact Nat.lt_pow_succ_log_self (by norm_num) n

theorem strictDyadicRoot_le_of_lt_pow {n J : ℕ} (hn : 0 < n)
    (hJ : n < 2 ^ J) : strictDyadicRoot n ≤ J := by
  have hl : Nat.log 2 n < J := Nat.log_lt_of_lt_pow (Nat.ne_of_gt hn) hJ
  dsimp [strictDyadicRoot]
  omega

theorem strictDyadicRoot_monotone : Monotone strictDyadicRoot := by
  intro n m h
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem strictDyadicRoot_two_pow (h : ℕ) :
    strictDyadicRoot (2 ^ h) = h + 1 := by
  simp [strictDyadicRoot, Nat.log_pow]

/-- The explicit cut used to pay the new endpoint when multiplying E(n) by a letter. -/
theorem exists_endpoint_cut (n : ℕ) (hn : 0 < n) :
    ∃ m i δ : ℕ,
      0 < m ∧ i < 2 ^ m ∧
      n = (2 ^ m - 1) + i ∧
      δ = 2 ^ m - i ∧
      δ = 2 ^ strictDyadicRoot (n + 1) - (n + 1) ∧
      strictDyadicRoot (n + 1) = m + 1 := by
  let m := Nat.log 2 (n + 1)
  let q := 2 ^ m
  have hq : q ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
  have hupper : n + 1 < q * 2 := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n + 1)
    simpa [q, m, pow_succ] using h
  have hqpos : 0 < q := pow_pos (by norm_num) _
  have hm : 0 < m := by
    have htwo : (2 : ℕ) ^ 1 ≤ n + 1 := by norm_num; omega
    have hl := Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) htwo
    change 0 < Nat.log 2 (n + 1)
    omega
  refine ⟨m, n + 1 - q, q - (n + 1 - q), hm, ?_, ?_, rfl, ?_, ?_⟩
  · change n + 1 - q < q
    omega
  · change n = (q - 1) + (n + 1 - q)
    omega
  · change q - (n + 1 - q) = 2 ^ (m + 1) - (n + 1)
    rw [pow_succ]
    change q - (n + 1 - q) = q * 2 - (n + 1)
    omega
  · rfl

end CriticalGK2.Actual
