import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.List.Defs

/-!
# Exact residual-word consumption

`consumePrefix p w` returns the unique suffix after consuming a prescribed
initial word p, or fails if no such suffix exists.  This explicit recursion
will describe the deterministic internal part of the suffix-trie automaton.
-/

namespace CriticalGK2.Automaton

def consumePrefix : List Bool → List Bool → Option (List Bool)
  | [], w => some w
  | _ :: _, [] => none
  | a :: p, b :: w => if a = b then consumePrefix p w else none

@[simp]
theorem consumePrefix_nil (w : List Bool) : consumePrefix [] w = some w := rfl

/-- Successful word consumption is equivalent to word concatenation. -/
theorem consumePrefix_eq_some_iff (p w t : List Bool) :
    consumePrefix p w = some t ↔ w = p ++ t := by
  induction p generalizing w with
  | nil => simp [consumePrefix]
  | cons a p ih =>
    cases w with
    | nil => simp [consumePrefix]
    | cons b w =>
      cases a <;> cases b <;> simp [consumePrefix, ih]

@[simp]
theorem consumePrefix_append (p t : List Bool) :
    consumePrefix p (p ++ t) = some t :=
  (consumePrefix_eq_some_iff p (p ++ t) t).mpr rfl

theorem length_le_of_consumePrefix_eq_some (p w t : List Bool)
    (h : consumePrefix p w = some t) : t.length ≤ w.length := by
  have hw := (consumePrefix_eq_some_iff p w t).mp h
  rw [hw, List.length_append]
  omega

theorem consumePrefix_none_no_append (p w : List Bool)
    (h : consumePrefix p w = none) : ¬ ∃ t, w = p ++ t := by
  rintro ⟨t, ht⟩
  have hs := (consumePrefix_eq_some_iff p w t).mpr ht
  rw [h] at hs
  contradiction

end CriticalGK2.Automaton
