import CriticalGK2.PrimeCriticalEndpoint

/-!
# The field-only default existence theorem

The envelope is the actual natural-number cast n ↦ (n : ℝ), whose eventual
lower bound is already proved. Its monotonicity and positive-degree lower
bound are discharged here. The displayed predicate lists properties of
one literal augmentation-kernel quotient and its actual maps. It is the
conclusion of the existence theorem. Its positive-degree index n represents
degree n+1.
-/

namespace CriticalGK2.Actual

noncomputable section

open Filter
open TensorProduct

variable (F : Type*) [Field F]

/-- All properties below concern the same actual non-unital positive quotient. -/
def DefaultPrimeCriticalProperties
    (I : TwoSidedIdeal (WordAlgebra F))
    (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)
    (hEI : allCutTwoSidedIdeal F
      (sparseDualData F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges)
      (sparseDualData_primalCoherent F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges) ≤ I) :
    Prop :=
      WordIdealHomogeneous F I ∧ NoWordTail F I ∧
      (NonUnitalAlgebra.adjoin F (Set.range
        (positiveIdealGenerator F I hpos (sparseDualData F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges)
          (sparseDualData_primalCoherent F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges) hEI)) = ⊤) ∧
      (∀ b : Bool, positiveIdealGenerator F I hpos (sparseDualData F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges)
        (sparseDualData_primalCoherent F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges) hEI b ∈ positiveIdealDegreeSpace F I hpos 0) ∧
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
        (positiveIdealDegreeGrowth F I hpos n : ℝ) ≤ 4 * ((n : ℝ) + 1) ^ 2 * (n : ℝ)) ∧
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
          positivePower M N = 0)

/-- A complete existence theorem with only a field as input. -/
theorem exists_prime_critical_gk_two_absolute_nil_default :
    ∃ I : TwoSidedIdeal (WordAlgebra F),
      ∃ hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0,
      ∃ hEI : allCutTwoSidedIdeal F
        (sparseDualData F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges)
        (sparseDualData_primalCoherent F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges) ≤ I,
        DefaultPrimeCriticalProperties F I hpos hEI := by
  have hmono : Monotone (fun n : ℕ => (n : ℝ)) := by
    intro a b hab
    change (a : ℝ) ≤ (b : ℝ)
    exact_mod_cast hab
  have hone : ∀ n : ℕ, 0 < n → 1 ≤ (n : ℝ) := by
    intro n hn
    have hn' : 1 ≤ n := by omega
    exact_mod_cast hn'
  simpa only [DefaultPrimeCriticalProperties] using
    exists_prime_critical_gk_two_absolute_nil F (fun n : ℕ => (n : ℝ))
      linearEnvelope_diverges hmono hone

#print CriticalGK2.Actual.DefaultPrimeCriticalProperties
#check CriticalGK2.Actual.exists_prime_critical_gk_two_absolute_nil_default
#print axioms CriticalGK2.Actual.exists_prime_critical_gk_two_absolute_nil_default

end

end CriticalGK2.Actual
