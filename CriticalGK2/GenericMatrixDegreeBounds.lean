import CriticalGK2.GenericMatrixCoefficients

/-!
# Actual degree window of a generic matrix power

Every monomial of a generic entry has degree in `[1,d]`.  The actual
noncommutative power therefore has support in `[e,d*e]`. The proof uses the
word-convolution recurrence.
-/

namespace CriticalGK2.Automaton

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R] {r d : ℕ}

/-- An actual nonempty word has coefficient zero in the algebraic unit. -/
theorem unit_cons_word_coefficient (α : Bool) (w : List Bool) :
    (1 : MonoidAlgebra R (FreeMonoid Bool)) (FreeMonoid.ofList (α :: w)) = 0 := by
  have hne : FreeMonoid.ofList (α :: w) ≠ (1 : FreeMonoid Bool) := by
    intro h
    have hl := congrArg FreeMonoid.toList h
    simp at hl
  simp [MonoidAlgebra.one_def, MonoidAlgebra.single_apply, hne, Ne.symm hne]

/-- The actual power has no word of degree smaller than the power exponent. -/
theorem genericMatrix_pow_coefficient_eq_zero_of_length_lt
    (c : Coefficients R r d) (e : ℕ) (w : List Bool) (a b : Fin r)
    (hw : w.length < e) :
    (((genericMatrix c) ^ e) a b) (FreeMonoid.ofList w) = 0 := by
  classical
  induction e generalizing w a b with
  | zero => omega
  | succ e ih =>
    cases w with
    | nil => exact genericMatrix_pow_succ_nil_coefficient c e a b
    | cons α w =>
      rw [genericMatrix_pow_succ_cons_coefficient]
      apply Finset.sum_eq_zero
      intro s _
      cases hc : consumePrefix s.2.val w with
      | none => simp [afterConsume, hc]
      | some t =>
        have ht : t.length < e := by
          have hle := length_le_of_consumePrefix_eq_some s.2.val w t hc
          simp only [List.length_cons] at hw
          omega
        simp [afterConsume, hc, ih t s.1 b ht]

/-- The actual power has no word of degree larger than `d` times its exponent. -/
theorem genericMatrix_pow_coefficient_eq_zero_of_mul_lt_length
    (c : Coefficients R r d) (e : ℕ) (w : List Bool) (a b : Fin r)
    (hw : d * e < w.length) :
    (((genericMatrix c) ^ e) a b) (FreeMonoid.ofList w) = 0 := by
  classical
  induction e generalizing w a b with
  | zero =>
    cases w with
    | nil => simp at hw
    | cons α w =>
      simp only [pow_zero, Matrix.one_apply]
      by_cases hab : a = b
      · rw [if_pos hab]
        exact unit_cons_word_coefficient α w
      · rw [if_neg hab]
        rfl
  | succ e ih =>
    cases w with
    | nil => simp at hw
    | cons α w =>
      rw [genericMatrix_pow_succ_cons_coefficient]
      apply Finset.sum_eq_zero
      intro s _
      cases hc : consumePrefix s.2.val w with
      | none => simp [afterConsume, hc]
      | some t =>
        have hdecomp : w.length = s.2.val.length + t.length := by
          rw [(consumePrefix_eq_some_iff s.2.val w t).mp hc, List.length_append]
        have hp : s.2.val.length < d := s.2.property
        have ht : d * e < t.length := by
          simp only [List.length_cons, Nat.mul_succ] at hw
          omega
        simp [afterConsume, hc, ih t s.1 b ht]

/-- The complete actual support window, including the empty-word boundary. -/
theorem genericMatrix_pow_coefficient_eq_zero_outside_window
    (c : Coefficients R r d) (e : ℕ) (w : List Bool) (a b : Fin r)
    (hw : w.length < e ∨ d * e < w.length) :
    (((genericMatrix c) ^ e) a b) (FreeMonoid.ofList w) = 0 := by
  rcases hw with hw | hw
  · exact genericMatrix_pow_coefficient_eq_zero_of_length_lt c e w a b hw
  · exact genericMatrix_pow_coefficient_eq_zero_of_mul_lt_length c e w a b hw

#print axioms CriticalGK2.Automaton.genericMatrix_pow_coefficient_eq_zero_outside_window

end

end CriticalGK2.Automaton
