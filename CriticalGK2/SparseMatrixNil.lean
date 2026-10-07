import CriticalGK2.SparseConstruction
import CriticalGK2.FamilyEventReadback
import CriticalGK2.MatrixNilReadback
import CriticalGK2.VersionOne

/-!
# Constructed matrix nilness over the original field

The actual infinite polynomial family supplies both long completion kernels.
The all-cut semantic premise of MatrixNilReadback is thereby discharged for
one actual positive quotient. The unitization endpoint uses this proved nil
statement. Growth, GK dimension and scalar extensions are separate obligations.
-/

namespace CriticalGK2.Actual

noncomputable section

open CriticalGK2.Automaton

variable (F : Type*) [Field F]

/-- One exponent for each positive matrix-size/degree pair kills all actual
cut annihilators, for every coefficient algebra and every letter assignment. -/
theorem sparse_allCut_evaluation_zero (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d) :
    ∃ N : ℕ, ∀ (C : Type*) [CommRing C] [Algebra F C]
      (v : Bool → Matrix (Fin (stateNumber r d)) (Fin (stateNumber r d)) C),
      ∀ n : ℕ, N ≤ n →
      (homogeneousAllCutComponent F (sparseDualData F Λ hΛ) n).dualAnnihilator ≤
        LinearMap.ker (actualDualMatrixEvaluation F C (stateNumber r d) n v) := by
  obtain ⟨H, hH⟩ := sparse_all_automata_endpoint F Λ hΛ r d hr hd
  refine ⟨2 * 2 ^ H, ?_⟩
  intro C _ _ v n hn
  exact actualDualFamily_allCut_evaluation_zero_of_event F C (stateNumber r d) v
    (infiniteSpace F (scheduledWaiting Λ hΛ) targetSize)
    (infiniteSpace_le_homogeneous F (scheduledWaiting Λ hΛ) targetSize)
    (infiniteSpace_coherent F (scheduledWaiting Λ hΛ) targetSize)
    H n (hH C v) hn

/-- Every positive-order matrix over the constructed non-unital quotient
is nilpotent. -/
theorem sparse_positive_matrix_nil (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) :
    ∀ r : ℕ, 0 < r →
      ∀ M : Matrix (Fin r) (Fin r)
        (PositiveAllCutQuotient F (sparseDualData F Λ hΛ)
          (sparseDualData_primalCoherent F Λ hΛ)),
        ∃ e : ℕ, positivePower M e = 0 := by
  apply positive_matrix_nil_of_allCut_evaluation_zero F (sparseDualData F Λ hΛ)
    (sparseDualData_primalCoherent F Λ hΛ)
  intro r hr d hd
  obtain ⟨N, hN⟩ := sparse_allCut_evaluation_zero F Λ hΛ r d hr hd
  exact ⟨N, fun c n hn => hN (Polynomial F) (finiteLetterTransition c) n hn⟩

/-- All positive-order matrices over the unitization of the sparse quotient
are algebraic over the base field. -/
theorem sparse_unitization_matrix_algebraic (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) :
    ∀ r : ℕ, 0 < r →
      Algebra.IsAlgebraic F (Matrix (Fin r) (Fin r)
        (Unitization F (PositiveAllCutQuotient F (sparseDualData F Λ hΛ)
          (sparseDualData_primalCoherent F Λ hΛ)))) :=
  CriticalGK2.VersionOne.capstone (sparse_positive_matrix_nil F Λ hΛ)

/-- A fully specified envelope supplies the ordinary scheduling input. -/
theorem linearEnvelope_diverges : EnvelopeDiverges (fun n : ℕ => (n : ℝ)) := by
  intro M
  obtain ⟨N, hN⟩ := exists_nat_ge M
  refine ⟨N, fun n hn => hN.trans ?_⟩
  change (N : ℝ) ≤ (n : ℝ)
  exact_mod_cast hn

/-- The explicit positive quotient used at the original-field existence
endpoint. Only standard inherited operations are used. -/
abbrev OriginalFieldNilAlgebra :=
  PositiveAllCutQuotient F
    (sparseDualData F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges)
    (sparseDualData_primalCoherent F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges)

/-- The constructed algebra over the original field is infinite dimensional,
all its matrix orders are nil, and all matrix orders of its unitization are
algebraic. -/
theorem originalField_endpoint :
    (¬ Module.Finite F (OriginalFieldNilAlgebra F)) ∧
    (∀ r : ℕ, 0 < r → ∀ M : Matrix (Fin r) (Fin r) (OriginalFieldNilAlgebra F),
      ∃ e : ℕ, positivePower M e = 0) ∧
    (∀ r : ℕ, 0 < r → Algebra.IsAlgebraic F
      (Matrix (Fin r) (Fin r) (Unitization F (OriginalFieldNilAlgebra F)))) := by
  refine ⟨?_, sparse_positive_matrix_nil F _ linearEnvelope_diverges,
    sparse_unitization_matrix_algebraic F _ linearEnvelope_diverges⟩
  exact constructed_positive_not_finite F _ _

#print axioms CriticalGK2.Actual.sparse_allCut_evaluation_zero
#print axioms CriticalGK2.Actual.sparse_positive_matrix_nil
#print axioms CriticalGK2.Actual.sparse_unitization_matrix_algebraic
#print axioms CriticalGK2.Actual.originalField_endpoint

end

end CriticalGK2.Actual
