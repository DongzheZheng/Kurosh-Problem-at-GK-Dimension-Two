import CriticalGK2.SuffixAutomaton
import Mathlib

/-!
# Actual generic matrix coefficients and the finite automaton

The matrix in this file is a matrix over the actual free monoid algebra.
Its entries contain exactly the positive words of lengths at most `d`.
The automaton identity is proved from single-word convolution, deterministic
residual consumption, and strong induction on the input word length.
-/

namespace CriticalGK2.Automaton

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R] {r d : ℕ}

/-- Taking an actual free-word coefficient commutes with a finite sum. -/
theorem wordCoefficient_sum {ι : Type*} (s : Finset ι)
    (f : ι → MonoidAlgebra R (FreeMonoid Bool)) (w : FreeMonoid Bool) :
    (∑ i ∈ s, f i) w = ∑ i ∈ s, f i w := by
  let ev : MonoidAlgebra R (FreeMonoid Bool) →+ R :=
    { toFun := fun P => P w
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum ev f s

/-- An actual entry of the generic matrix.  The pair `(α,p)` parametrizes
all nonempty words of length at most `d` without repetition. -/
def genericEntry (c : Coefficients R r d) (a b : Fin r) :
    MonoidAlgebra R (FreeMonoid Bool) :=
  ∑ α : Bool, ∑ p : Residual d,
    MonoidAlgebra.single (FreeMonoid.ofList (α :: p.val)) (c a b α p)

/-- The actual matrix whose powers are encoded by the automaton. -/
def genericMatrix (c : Coefficients R r d) :
    Matrix (Fin r) (Fin r) (MonoidAlgebra R (FreeMonoid Bool)) :=
  genericEntry c

/-- Scalar multiplication can be performed after exact prefix consumption. -/
theorem mul_afterConsume (p w : List Bool) (c : R) (f : List Bool → R) :
    c * afterConsume p w f = afterConsume p w (fun t => c * f t) := by
  cases hc : consumePrefix p w <;> simp [afterConsume, hc]

/-- Polynomial coefficient extraction can be performed after exact prefix consumption. -/
theorem coeff_afterConsume (p w : List Bool) (f : List Bool → Polynomial R) (e : ℕ) :
    (afterConsume p w f).coeff e = afterConsume p w (fun t => (f t).coeff e) := by
  cases hc : consumePrefix p w <;> simp [afterConsume, hc]

/-- Prefix consumption respects an equality on every successful residual. -/
theorem afterConsume_congr {T : Type*} [Zero T] (p w : List Bool)
    (f g : List Bool → T)
    (h : ∀ t, consumePrefix p w = some t → f t = g t) :
    afterConsume p w f = afterConsume p w g := by
  cases hc : consumePrefix p w with
  | none => simp [afterConsume, hc]
  | some t => simp only [afterConsume, hc]; exact h t hc

/-- Left multiplication by a generic entry satisfies the word-convolution
recurrence. -/
theorem genericEntry_mul_cons_coefficient (c : Coefficients R r d)
    (α : Bool) (w : List Bool) (a j : Fin r)
    (P : MonoidAlgebra R (FreeMonoid Bool)) :
    (genericEntry c a j * P) (FreeMonoid.ofList (α :: w)) =
      ∑ p : Residual d,
        afterConsume p.val w (fun t => c a j α p * P (FreeMonoid.ofList t)) := by
  classical
  rw [genericEntry, Finset.sum_mul, wordCoefficient_sum]
  simp_rw [Finset.sum_mul, wordCoefficient_sum, single_word_mul_coefficient]
  cases α <;> simp [Fintype.sum_bool, afterConsume, consumePrefix]

/-- Positivity of every generic-entry monomial excludes the empty word. -/
theorem genericEntry_mul_nil_coefficient (c : Coefficients R r d)
    (a j : Fin r) (P : MonoidAlgebra R (FreeMonoid Bool)) :
    (genericEntry c a j * P) (FreeMonoid.ofList []) = 0 := by
  classical
  rw [genericEntry, Finset.sum_mul, wordCoefficient_sum]
  simp_rw [Finset.sum_mul, wordCoefficient_sum, single_word_mul_coefficient]
  simp [afterConsume, consumePrefix]

/-- The genuine matrix power has the head recurrence at each word. -/
theorem genericMatrix_pow_succ_cons_coefficient (c : Coefficients R r d)
    (e : ℕ) (α : Bool) (w : List Bool) (a b : Fin r) :
    (((genericMatrix c) ^ (e + 1)) a b) (FreeMonoid.ofList (α :: w)) =
      ∑ s : State r d, afterConsume s.2.val w
        (fun t => c a s.1 α s.2 *
          (((genericMatrix c) ^ e) s.1 b) (FreeMonoid.ofList t)) := by
  classical
  rw [pow_succ', Matrix.mul_apply, wordCoefficient_sum]
  simp_rw [genericMatrix, genericEntry_mul_cons_coefficient]
  exact (Fintype.sum_prod_type (fun s : Fin r × Residual d =>
    afterConsume s.2.val w (fun t => c a s.1 α s.2 *
      (((genericMatrix c) ^ e) s.1 b) (FreeMonoid.ofList t)))).symm

/-- Positive powers have zero empty-word coefficient. -/
theorem genericMatrix_pow_succ_nil_coefficient (c : Coefficients R r d)
    (e : ℕ) (a b : Fin r) :
    (((genericMatrix c) ^ (e + 1)) a b) (FreeMonoid.ofList []) = 0 := by
  classical
  rw [pow_succ', Matrix.mul_apply, wordCoefficient_sum]
  apply Finset.sum_eq_zero
  intro j _
  exact genericEntry_mul_nil_coefficient c a j (((genericMatrix c) ^ e) j b)

/-- No head-to-head nonempty path uses zero completed generic monomials. -/
theorem headValue_cons_coeff_zero (c : Coefficients R r d) (hd : 0 < d)
    (α : Bool) (w : List Bool) (a b : Fin r) :
    (headValue c hd (α :: w) a b).coeff 0 = 0 := by
  rw [headValue_cons, Polynomial.finset_sum_coeff]
  simp [Polynomial.mul_coeff_zero]

/-- Exact polynomial-coefficient head recurrence of the actual automaton. -/
theorem headValue_cons_coeff_succ (c : Coefficients R r d) (hd : 0 < d)
    (e : ℕ) (α : Bool) (w : List Bool) (a b : Fin r) :
    (headValue c hd (α :: w) a b).coeff (e + 1) =
      ∑ s : State r d, afterConsume s.2.val w
        (fun t => c a s.1 α s.2 * (headValue c hd t s.1 b).coeff e) := by
  classical
  rw [headValue_cons, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro s _
  rw [Polynomial.coeff_monomial_mul, coeff_afterConsume, mul_afterConsume]

/-- The automaton identity for arbitrary coefficients in a commutative ring,
relating transition-matrix products to generic matrix-power coefficients. -/
theorem headValue_coeff_eq_genericMatrix_pow_coefficient
    (c : Coefficients R r d) (hd : 0 < d) (w : List Bool)
    (e : ℕ) (a b : Fin r) :
    (headValue c hd w a b).coeff e =
      (((genericMatrix c) ^ e) a b) (FreeMonoid.ofList w) := by
  classical
  have hmain : ∀ n : ℕ, ∀ w : List Bool, w.length = n →
      ∀ e : ℕ, ∀ a b : Fin r,
      (headValue c hd w a b).coeff e =
        (((genericMatrix c) ^ e) a b) (FreeMonoid.ofList w) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hwn e a b
      cases w with
      | nil =>
        cases e with
        | zero =>
          by_cases hab : a = b <;>
            simp [headValue_nil, hab, Matrix.one_apply, MonoidAlgebra.one_def,
              MonoidAlgebra.single_apply] <;> rfl
        | succ e =>
          rw [genericMatrix_pow_succ_nil_coefficient]
          by_cases hab : a = b <;> simp [headValue_nil, hab, Polynomial.coeff_one]
      | cons α w =>
        cases e with
        | zero =>
          rw [headValue_cons_coeff_zero]
          have hne : FreeMonoid.ofList (α :: w) ≠ (1 : FreeMonoid Bool) := by
            intro h
            have hl := congrArg FreeMonoid.toList h
            simp at hl
          have hcoef : (1 : MonoidAlgebra R (FreeMonoid Bool))
              (FreeMonoid.ofList (α :: w)) = 0 := by
            rw [MonoidAlgebra.one_def, MonoidAlgebra.single_apply, if_neg (Ne.symm hne)]
          by_cases hab : a = b
          · simpa only [pow_zero, Matrix.one_apply, if_pos hab] using hcoef.symm
          · simp [Matrix.one_apply, hab] <;> rfl
        | succ e =>
          rw [headValue_cons_coeff_succ, genericMatrix_pow_succ_cons_coefficient]
          apply Finset.sum_congr rfl
          intro s _
          apply afterConsume_congr
          intro t ht
          have hlen : t.length < n := by
            have hle := length_le_of_consumePrefix_eq_some s.2.val w t ht
            simp only [List.length_cons] at hwn
            omega
          rw [ih t.length hlen t rfl e s.1 b]
  exact hmain w.length w rfl e a b

/-- Independent generic coefficients indexed by source, destination and the
unique first-letter/residual decomposition of every allowed monomial. -/
abbrev CoefficientIndex (r d : ℕ) := Fin r × Fin r × Bool × Residual d

abbrev GenericCoefficientRing (F : Type*) [CommRing F] (r d : ℕ) :=
  MvPolynomial (CoefficientIndex r d) F

def independentCoefficients (F : Type*) [CommRing F] (r d : ℕ) :
    Coefficients (GenericCoefficientRing F r d) r d :=
  fun a b α p => MvPolynomial.X (a, b, α, p)

/-- Specialization of the proved identity to the actual polynomial ring
`F[c][u]` used for universal nilpotence and extension-field readback. -/
theorem generic_automaton_coefficient_identity (F : Type*) [CommRing F]
    (r d : ℕ) (hd : 0 < d) (w : List Bool) (e : ℕ) (a b : Fin r) :
    (headValue (independentCoefficients F r d) hd w a b).coeff e =
      (((genericMatrix (independentCoefficients F r d)) ^ e) a b)
        (FreeMonoid.ofList w) :=
  headValue_coeff_eq_genericMatrix_pow_coefficient
    (independentCoefficients F r d) hd w e a b

#print axioms CriticalGK2.Automaton.headValue_coeff_eq_genericMatrix_pow_coefficient
#print axioms CriticalGK2.Automaton.generic_automaton_coefficient_identity

end

end CriticalGK2.Automaton
