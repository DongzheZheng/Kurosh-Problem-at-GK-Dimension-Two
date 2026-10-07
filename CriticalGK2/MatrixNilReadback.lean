import CriticalGK2.SameFieldReadback
import CriticalGK2.CutDuality
import CriticalGK2.MatrixQuotientDescent
import CriticalGK2.GenericMatrixCoverage

/-!
# Actual matrix-power absorption from all-cut automaton vanishing

The exponent is N+1, agreeing exactly with `positivePower M N`. Degrees below
N+1 vanish by positivity of the generic entry words. Every remaining degree
is read back through the actual annihilator and finite homogeneous summation.
The long-block theorem supplies all-cut vanishing for the construction.
-/

namespace CriticalGK2.Actual

noncomputable section

open CriticalGK2.Automaton

variable (F : Type*) [Field F]

theorem genericPositivePower_mem_allCutSubmodule
    (W : DyadicDualData F) (r d N : ℕ) (hd : 0 < d)
    (c : Coefficients F r d)
    (hzero : ∀ n : ℕ, N ≤ n →
      (homogeneousAllCutComponent F W n).dualAnnihilator ≤
        LinearMap.ker (actualDualMatrixEvaluation F (Polynomial F) (stateNumber r d) n
          (finiteLetterTransition c))) :
    ∀ a b : Fin r, (positivePower (genericMatrix c) N) a b ∈ allCutSubmodule F W := by
  intro a b
  rw [positivePower_eq_pow]
  apply mem_allCutSubmodule_of_homogeneousProjections_mem F W
  intro n
  by_cases hn : n < N + 1
  · rw [homogeneousProjection_genericPower_eq_zero_of_lt F c n (N + 1) a b hn]
    exact (allCutComponent F W n).zero_mem
  · have hNn : N ≤ n := by omega
    have hmem := homogeneousProjection_genericPower_mem_of_evaluation_zero F c hd n (N + 1)
      a b (homogeneousAllCutComponent F W n) (fun φ hφ => hzero n hNn hφ)
    exact hmem

/-- Positive word matrices have ideal-valued powers under universal all-cut
evaluator vanishing. Their generic representation is obtained from the
entries' finite word support. -/
theorem wordMatrix_positivePower_absorption_of_allCut_evaluation_zero
    (W : DyadicDualData F) (r : ℕ)
    (hzero : ∀ d : ℕ, 0 < d → ∃ N : ℕ,
      ∀ c : Coefficients F r d, ∀ n : ℕ, N ≤ n →
      (homogeneousAllCutComponent F W n).dualAnnihilator ≤
        LinearMap.ker (actualDualMatrixEvaluation F (Polynomial F) (stateNumber r d) n
          (finiteLetterTransition c)))
    (M : Matrix (Fin r) (Fin r) (WordAlgebra F))
    (hpositive : ∀ a b, augmentation F (M a b) = 0) :
    ∃ N : ℕ, ∀ a b : Fin r, (positivePower M N) a b ∈ allCutSubmodule F W := by
  have hcoeff : ∀ a b, M a b 1 = 0 := by
    intro a b
    simpa only [augmentation_eq_constantCoeff] using hpositive a b
  obtain ⟨d, hd, c, hc⟩ := exists_genericMatrix_representation M hcoeff
  obtain ⟨N, hN⟩ := hzero d hd
  refine ⟨N, ?_⟩
  rw [← hc]
  exact genericPositivePower_mem_allCutSubmodule F W r d N hd c (hN c)

/-- Universal all-cut evaluator vanishing in every finite automaton order
and degree implies nilpotence of quotient matrices. -/
theorem positive_matrix_nil_of_allCut_evaluation_zero
    (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (hzero : ∀ r : ℕ, 0 < r → ∀ d : ℕ, 0 < d → ∃ N : ℕ,
      ∀ c : Coefficients F r d, ∀ n : ℕ, N ≤ n →
      (homogeneousAllCutComponent F W n).dualAnnihilator ≤
        LinearMap.ker (actualDualMatrixEvaluation F (Polynomial F) (stateNumber r d) n
          (finiteLetterTransition c))) :
    ∀ r : ℕ, 0 < r →
      ∀ M : Matrix (Fin r) (Fin r) (PositiveAllCutQuotient F W hW),
        ∃ N : ℕ, positivePower M N = 0 := by
  intro r hr M
  obtain ⟨L, hL, hmap⟩ := exists_positive_wordMatrix_lift F W hW r M
  obtain ⟨N, hN⟩ := wordMatrix_positivePower_absorption_of_allCut_evaluation_zero F W r
    (hzero r hr) L hL
  exact ⟨N, positiveMatrixPower_eq_zero_of_lift F W hW r M L hmap N hN⟩

#print axioms CriticalGK2.Actual.genericPositivePower_mem_allCutSubmodule
#print axioms CriticalGK2.Actual.positive_matrix_nil_of_allCut_evaluation_zero

end

end CriticalGK2.Actual
