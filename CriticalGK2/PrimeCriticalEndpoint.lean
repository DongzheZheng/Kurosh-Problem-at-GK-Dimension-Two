import CriticalGK2.PositiveWordIdealWordProducts
import CriticalGK2.PositiveWordIdealGrading
import CriticalGK2.PositiveWordIdealUniformDegree
import CriticalGK2.PositiveWordIdealJustInfinite

/-!
# The actual prime critical-growth construction

The only inputs of the existence theorem are a field and an admissible
prescribed growth envelope. Its witness is a literal ideal of the two-letter
word algebra, and Q is the literal augmentation kernel in H/I. Homogeneity,
survival, primeness, nilness, generation, grading and all growth estimates
are derived for that same Q. The positive space with index m has degree m+1.
The positive-power index e denotes the ordinary positive exponent e+1.
-/

namespace CriticalGK2.Actual

noncomputable section

open Filter
open TensorProduct

variable (F : Type*) [Field F]

theorem exists_prime_critical_gk_two_absolute_nil (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (hmono : Monotone Λ)
    (hone : ∀ n : ℕ, 0 < n → 1 ≤ Λ n) :
    ∃ I : TwoSidedIdeal (WordAlgebra F),
      ∃ hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0,
      ∃ hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
        (sparseDualData_primalCoherent F Λ hΛ) ≤ I,
      WordIdealHomogeneous F I ∧ NoWordTail F I ∧
      (NonUnitalAlgebra.adjoin F (Set.range
        (positiveIdealGenerator F I hpos (sparseDualData F Λ hΛ)
          (sparseDualData_primalCoherent F Λ hΛ) hEI)) = ⊤) ∧
      (∀ b : Bool, positiveIdealGenerator F I hpos (sparseDualData F Λ hΛ)
        (sparseDualData_primalCoherent F Λ hΛ) hEI b ∈ positiveIdealDegreeSpace F I hpos 0) ∧
      (¬ Module.Finite F (PositiveWordIdealQuotient F I hpos)) ∧
      CriticalGK2.PrimeInheritance.OrdinaryNonUnitalPrime (PositiveWordIdealQuotient F I hpos) ∧
      DirectSum.IsInternal (positiveIdealDegreeSpace F I hpos) ∧
      (∀ m n : ℕ, ∀ x y : PositiveWordIdealQuotient F I hpos,
        x ∈ positiveIdealDegreeSpace F I hpos m →
        y ∈ positiveIdealDegreeSpace F I hpos n →
        x * y ∈ positiveIdealDegreeSpace F I hpos (m + n + 1)) ∧
      (∀ J : Submodule F (PositiveWordIdealQuotient F I hpos), J ≠ ⊥ →
        (∀ a b : PositiveWordIdealQuotient F I hpos, b ∈ J → a * b ∈ J) →
        (∀ a b : PositiveWordIdealQuotient F I hpos, a ∈ J → a * b ∈ J) →
        J = (⨆ n : ℕ, J ⊓ positiveIdealDegreeSpace F I hpos n) →
        Module.Finite F ((PositiveWordIdealQuotient F I hpos) ⧸ J)) ∧
      (∀ a : PositiveWordIdealQuotient F I hpos, a ≠ 0 →
        ∃ N : ℕ, 0 < N ∧ Module.Finite F (CriticalGK2.GenericResidual.Truncation F I N) ∧
          ((CriticalGK2.GenericResidual.factor F I N).toNonUnitalAlgHom.comp
            (positiveWordIdealInclusion F I hpos)) a ≠ 0) ∧
      (∀ n : ℕ, n * (n + 3) ≤ 2 * positiveIdealDegreeGrowth F I hpos n) ∧
      (∀ n : ℕ, 0 < n →
        (positiveIdealDegreeGrowth F I hpos n : ℝ) ≤ 4 * ((n : ℝ) + 1) ^ 2 * Λ n) ∧
      (Filter.limsup (CriticalGK2.Growth.logarithmicGrowthRatio
        (positiveIdealDegreeGrowth F I hpos)) atTop = 2) ∧
      (∀ (K : Type*) [Field K] [Algebra F K],
        (∀ r : ℕ, 0 < r →
          ∀ M : Matrix (Fin r) (Fin r) ((PositiveWordIdealQuotient F I hpos) ⊗[F] K),
            ∃ e : ℕ, positivePower M e = 0) ∧
        (∀ r : ℕ, 0 < r → Algebra.IsAlgebraic K
          (Matrix (Fin r) (Fin r)
            (Unitization K (K ⊗[F] PositiveWordIdealQuotient F I hpos))))) ∧
      (∀ r d : ℕ, 0 < r → 0 < d → ∃ N : ℕ,
        ∀ (K : Type*) [Field K] [Algebra F K],
        ∀ M : Matrix (Fin r) (Fin r) ((PositiveWordIdealQuotient F I hpos) ⊗[F] K),
          (∀ a b, M a b ∈ positiveIdealScalarDegreeFiltration F K I hpos d) →
          positivePower M N = 0) := by
  obtain ⟨I, hEI, hhom, htail, hprime, hinfinite, hfinite, hlower⟩ :=
    sparse_exists_ordinaryPrime_furtherQuotient F Λ hΛ
  let hpos := homogeneous_noWordTail_augmentation_eq_zero F I hhom htail
  refine ⟨I, hpos, hEI, hhom, htail,
    positiveWordIdealQuotient_two_generated F I hpos (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) hEI,
    positiveIdealGenerator_mem_degree_one F I hpos (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) hEI,
    positiveWordIdealQuotient_not_finite F I hpos hinfinite,
    positiveWordIdealQuotient_ordinaryPrime F I hpos hprime htail,
    positiveIdealDegreeSpace_isInternal F I hpos hhom,
    positiveIdealDegreeSpace_mul_mem F I hpos,
    positiveWordIdealQuotient_graded_just_infinite F I hpos hhom hfinite,
    ?_, positive_furtherQuotient_growth_quadratic_lower F I hpos Λ hΛ hEI hhom htail,
    positive_furtherQuotient_envelope_upper F I hpos Λ hΛ hmono hone hEI,
    (positive_furtherQuotient_logarithmic_limit F I hpos Λ hΛ hEI hhom htail).limsup_eq,
    ?_, ?_⟩
  · intro a ha
    obtain ⟨N, hN, hsep⟩ := positiveWordIdealQuotient_residually_finite_dimensional
      F I hpos hhom a ha
    exact ⟨N, hN, inferInstance, hsep⟩
  · intro K _ _
    exact ⟨sparse_positiveWordIdeal_scalar_matrix_nil F K I hpos Λ hΛ hEI,
      sparse_positiveWordIdeal_scalar_unitization_matrix_algebraic F K I hpos Λ hΛ hEI⟩
  · intro r d hr hd
    exact sparse_uniform_positiveIdeal_bounded_scalar_matrix_nil F I hpos Λ hΛ hEI r d hr hd

#check CriticalGK2.Actual.exists_prime_critical_gk_two_absolute_nil
#print axioms CriticalGK2.Actual.exists_prime_critical_gk_two_absolute_nil

end

end CriticalGK2.Actual
