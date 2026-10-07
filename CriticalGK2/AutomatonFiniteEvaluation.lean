import CriticalGK2.GenericMatrixCoefficients
import CriticalGK2.MatrixPI

/-!
# Finite-index transport and actual free-algebra evaluation

The finite suffix automaton is transported to `Fin k` by an actual algebra
isomorphism of matrix algebras.  Its evaluation on every actual word equals
the transition-matrix product. The PI modules therefore apply to these
two finite matrices.
-/

namespace CriticalGK2.Automaton

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R] {r d : ℕ}

def stateNumber (r d : ℕ) : ℕ := Fintype.card (State r d)

/-- The actual number of states depends only on matrix size and degree bound. -/
theorem stateNumber_eq (r d : ℕ) :
    stateNumber r d = r * ∑ n : Fin d, (2 : ℕ) ^ n.val := by
  rw [stateNumber, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_congr (residualEquivVectors d), Fintype.card_sigma]
  simp

/-- The equivalence between the automaton state index and a finite ordinal. -/
def stateIndexEquiv (r d : ℕ) : State r d ≃ Fin (stateNumber r d) :=
  Fintype.equivFin (State r d)

/-- Actual algebra reindexing of the finite matrix algebra. -/
def finiteReindex (R : Type*) [CommRing R] (r d : ℕ) :
    Matrix (State r d) (State r d) (Polynomial R) ≃ₐ[Polynomial R]
      Matrix (Fin (stateNumber r d)) (Fin (stateNumber r d)) (Polynomial R) := by
  classical
  exact Matrix.reindexAlgEquiv (Polynomial R) (Polynomial R) (stateIndexEquiv r d)

def finiteHead (d : ℕ) (hd : 0 < d) (a : Fin r) : Fin (stateNumber r d) :=
  stateIndexEquiv r d (headState d hd a)

/-- The two actual `Fin k` matrices used as inputs to the matrix PI. -/
def finiteLetterTransition (c : Coefficients R r d) (α : Bool) :
    Matrix (Fin (stateNumber r d)) (Fin (stateNumber r d)) (Polynomial R) :=
  finiteReindex R r d (letterTransition c α)

def finiteWordTransition (c : Coefficients R r d) (w : List Bool) :
    Matrix (Fin (stateNumber r d)) (Fin (stateNumber r d)) (Polynomial R) :=
  finiteReindex R r d (wordTransition c w)

@[simp]
theorem finiteWordTransition_nil (c : Coefficients R r d) :
    finiteWordTransition c [] = 1 := by
  simp [finiteWordTransition]

@[simp]
theorem finiteWordTransition_cons (c : Coefficients R r d)
    (α : Bool) (w : List Bool) :
    finiteWordTransition c (α :: w) =
      finiteLetterTransition c α * finiteWordTransition c w := by
  simp [finiteWordTransition, finiteLetterTransition]

/-- The actual free-monoid homomorphism evaluates words to exactly the
actual transition-matrix product. -/
theorem finite_word_evaluation (c : Coefficients R r d) (w : List Bool) :
    FreeMonoid.lift (finiteLetterTransition c) (FreeMonoid.ofList w) =
      finiteWordTransition c w := by
  induction w with
  | nil => simp [FreeMonoid.lift_ofList]
  | cons α w ih =>
    rw [finiteWordTransition_cons]
    simpa only [FreeMonoid.lift_ofList, List.map_cons, List.prod_cons] using
      congrArg (fun M => finiteLetterTransition c α * M) ih

/-- Reindexing preserves each actual head-to-head entry. -/
theorem finiteWordTransition_head (c : Coefficients R r d) (hd : 0 < d)
    (w : List Bool) (a b : Fin r) :
    finiteWordTransition c w (finiteHead d hd a) (finiteHead d hd b) =
      headValue c hd w a b := by
  simp [finiteWordTransition, finiteReindex, Matrix.reindex_apply,
    Matrix.submatrix_apply, finiteHead, headValue]

/-- The proved generic coefficient identity for the actual `Fin k` matrices. -/
theorem finite_automaton_coefficient_identity (c : Coefficients R r d) (hd : 0 < d)
    (w : List Bool) (e : ℕ) (a b : Fin r) :
    (finiteWordTransition c w (finiteHead d hd a) (finiteHead d hd b)).coeff e =
      (((genericMatrix c) ^ e) a b) (FreeMonoid.ofList w) := by
  rw [finiteWordTransition_head]
  exact headValue_coeff_eq_genericMatrix_pow_coefficient c hd w e a b

/-- Actual free-algebra evaluation of a word with an arbitrary base-field
coefficient; this is the evaluator used by the actual-dual PI bridge. -/
theorem binaryEvaluation_single_finite_word (F : Type*) [CommRing F] [Algebra F R]
    (c : Coefficients R r d) (w : List Bool) (a : F) :
    CriticalGK2.binaryEvaluation F
        (Matrix (Fin (stateNumber r d)) (Fin (stateNumber r d)) (Polynomial R))
        (finiteLetterTransition c) (MonoidAlgebra.single (FreeMonoid.ofList w) a) =
      a • finiteWordTransition c w := by
  rw [CriticalGK2.binaryEvaluation, MonoidAlgebra.lift_single, finite_word_evaluation]

#print axioms CriticalGK2.Automaton.finite_automaton_coefficient_identity
#print axioms CriticalGK2.Automaton.binaryEvaluation_single_finite_word

end

end CriticalGK2.Automaton
