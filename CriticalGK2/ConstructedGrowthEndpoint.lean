import CriticalGK2.SparseGlobalCutBudget
import CriticalGK2.ActualEnvelopeGrowth
import CriticalGK2.ConstructedNilEndpoint

/-!
# The completely specified absolute nil algebra at growth exponent two

The actual global stage-budget theorem discharges the construction-specific
input of the growth connector. All statements refer to the same quotient
fixed over F before an arbitrary field extension is introduced. Its growth
is identified with the span of the actual nonempty words in its two original
degree-one generators. The defining upper-exponent set is nonempty and
bounded below by the already proved numerical endpoint.

The prime and graded just infinite refinements require the separate
homogeneous-ideal quotient construction.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F : Type*) [Field F]

theorem sparseDegreeGrowth_scheduled_upper (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (n : ℕ) (hn : 0 < n) :
    sparseDegreeGrowth F Λ hΛ n ≤ n * (n + 1) *
      supportBudget targetCost (begunOperationCount Λ hΛ (strictDyadicRoot n)) ^ 2 :=
  sparseDegreeGrowth_le_scheduled_budget_of_cutBounds F Λ hΛ
    (sparseDualData_cutBound F Λ hΛ) n hn

theorem sparseDegreeGrowth_near_two_upper (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (ε : ℝ) (hε : 0 < ε) :
    2 + ε ∈ CriticalGK2.Growth.UpperExponentSet (sparseDegreeGrowth F Λ hΛ) :=
  sparseDegreeGrowth_near_two_upper_of_cutBounds F Λ hΛ
    (sparseDualData_cutBound F Λ hΛ) ε hε

theorem sparseDegreeGrowth_gkExponent_eq_two (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) :
    CriticalGK2.Growth.GKExponent (sparseDegreeGrowth F Λ hΛ) = 2 :=
  sparseDegreeGrowth_gkExponent_eq_two_of_cutBounds F Λ hΛ
    (sparseDualData_cutBound F Λ hΛ)

theorem sparseDegreeGrowth_envelope_upper (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (hmono : Monotone Λ)
    (hone : ∀ n : ℕ, 0 < n → 1 ≤ Λ n) (n : ℕ) (hn : 0 < n) :
    (sparseDegreeGrowth F Λ hΛ n : ℝ) ≤ 4 * ((n : ℝ) + 1) ^ 2 * Λ n :=
  sparseDegreeGrowth_envelope_upper_of_cutBounds F Λ hΛ hmono hone
    (sparseDualData_cutBound F Λ hΛ) n hn

/-- Growth is the literal actual nonempty two-letter word-span dimension. -/
theorem originalFieldDegreeGrowth_eq_wordSpan_finrank (n : ℕ) :
    originalFieldDegreeGrowth F n = Module.finrank F
      (Submodule.span F (Set.range (boundedPositiveWordImage F
        (sparseDualData F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges)
        (sparseDualData_primalCoherent F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges) n))) :=
  positiveDegreeGrowth_eq_wordSpan_finrank F _ _ n

theorem originalFieldDegreeGrowth_gkExponent_eq_two :
    CriticalGK2.Growth.GKExponent (originalFieldDegreeGrowth F) = 2 :=
  sparseDegreeGrowth_gkExponent_eq_two F _ linearEnvelope_diverges

/-- Infinite dimension, two actual generators, exact growth exponent two,
quadratic lower growth, every upper exponent above two, absolute stable
nilness and algebraic matrix unitizations of the same fixed algebra. -/
theorem originalField_critical_gk_two_absolute_nil_endpoint :
    (¬ Module.Finite F (OriginalFieldNilAlgebra F)) ∧
    (NonUnitalAlgebra.adjoin F (Set.range (originalFieldGenerator F)) = ⊤) ∧
    (CriticalGK2.Growth.GKExponent (originalFieldDegreeGrowth F) = 2) ∧
    (∀ n : ℕ, n * (n + 3) ≤ 2 * originalFieldDegreeGrowth F n) ∧
    (∀ ε : ℝ, 0 < ε →
      2 + ε ∈ CriticalGK2.Growth.UpperExponentSet (originalFieldDegreeGrowth F)) ∧
    (∀ (K : Type*) [Field K] [Algebra F K],
      (∀ r : ℕ, 0 < r →
        ∀ M : Matrix (Fin r) (Fin r) ((OriginalFieldNilAlgebra F) ⊗[F] K),
          ∃ e : ℕ, positivePower M e = 0) ∧
      (∀ r : ℕ, 0 < r → Algebra.IsAlgebraic K
        (Matrix (Fin r) (Fin r) (Unitization K (K ⊗[F] (OriginalFieldNilAlgebra F)))))) := by
  obtain ⟨hinf, hgen, hext⟩ := originalField_constructed_absolute_nil_endpoint F
  exact ⟨hinf, hgen, originalFieldDegreeGrowth_gkExponent_eq_two F,
    originalFieldDegreeGrowth_quadratic_lower F,
    sparseDegreeGrowth_near_two_upper F _ linearEnvelope_diverges, hext⟩

#print axioms CriticalGK2.Actual.sparseDegreeGrowth_gkExponent_eq_two
#print axioms CriticalGK2.Actual.sparseDegreeGrowth_envelope_upper
#print axioms CriticalGK2.Actual.originalField_critical_gk_two_absolute_nil_endpoint

end

end CriticalGK2.Actual
