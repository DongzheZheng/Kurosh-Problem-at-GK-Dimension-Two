import CriticalGK2.GenericGradedGrowth
import CriticalGK2.ActualLogarithmicEndpoint

/-!
# Growth of the actual further homogeneous quotient

Its positive degree filtration is the literal image of the original positive
degree filtration under the actual factor map. Therefore the upper bound
passes to the new quotient by finite-dimensional linear algebra. The lower
bound was proved for the new quotient in GenericGradedGrowth. These two
actual bounds give the same logarithmic growth exponent two after the change
of quotient; survival and homogeneity remain ordinary ideal hypotheses.
-/

namespace CriticalGK2.Actual

noncomputable section

open Filter
open scoped Topology

variable (F : Type*) [Field F]

def furtherPositiveLinearMap (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (I : TwoSidedIdeal (WordAlgebra F)) (hEI : allCutTwoSidedIdeal F W hW ≤ I) :
    PositiveAllCutQuotient F W hW →ₗ[F] WordIdealQuotient F I :=
  (wordIdealFactorFromAllCut F W hW I hEI).toLinearMap.comp
    (positiveQuotientLinearInclusion F W hW)

theorem furtherPositiveLinearMap_homogeneous (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (I : TwoSidedIdeal (WordAlgebra F))
    (hEI : allCutTwoSidedIdeal F W hW ≤ I) (n : ℕ) (hn : n ≠ 0)
    (P : homogeneous F n) :
    furtherPositiveLinearMap F W hW I hEI (homogeneousToPositiveQuotient F W hW n hn P) =
      wordIdealQuotientMap F I P.val :=
  wordIdealFactorFromAllCut_map F W hW I hEI P.val

theorem idealDegreeSpace_eq_map_positiveSubspace (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (I : TwoSidedIdeal (WordAlgebra F))
    (hEI : allCutTwoSidedIdeal F W hW ≤ I) (m : ℕ) :
    idealDegreeSpace F I (m + 1) =
      (positiveDegreeSubspace F W hW m).map (furtherPositiveLinearMap F W hW I hEI) := by
  ext a
  constructor
  · intro ha
    obtain ⟨P, hP, hPa⟩ := Submodule.mem_map.mp ha
    let x : homogeneous F (m + 1) := ⟨P, hP⟩
    refine ⟨homogeneousToPositiveQuotient F W hW (m + 1) (by omega) x, ?_, ?_⟩
    · refine ⟨Submodule.Quotient.mk x, ?_⟩
      exact componentQuotientToPositive_mk F W hW (m + 1) (by omega) x
    · exact (furtherPositiveLinearMap_homogeneous F W hW I hEI (m + 1) (by omega) x).trans hPa
  · rintro ⟨a, ⟨q, rfl⟩, hqa⟩
    obtain ⟨P, hP⟩ := Submodule.Quotient.mk_surjective
      ((allCutComponent F W (m + 1)).comap (homogeneous F (m + 1)).subtype) q
    rw [← hP, componentQuotientToPositive_mk,
      furtherPositiveLinearMap_homogeneous] at hqa
    exact ⟨P.val, P.property, hqa⟩

theorem idealPositiveFiltration_eq_map (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (I : TwoSidedIdeal (WordAlgebra F))
    (hEI : allCutTwoSidedIdeal F W hW ≤ I) (N : ℕ) :
    idealPositiveDegreeFiltration F I N =
      (positiveDegreeFiltration F W hW N).map (furtherPositiveLinearMap F W hW I hEI) := by
  induction N with
  | zero => simp [idealPositiveDegreeFiltration, positiveDegreeFiltration]
  | succ N ih =>
      simp only [idealPositiveDegreeFiltration, positiveDegreeFiltration,
        Finset.range_add_one, Finset.sup_insert, Submodule.map_sup]
      rw [idealDegreeSpace_eq_map_positiveSubspace F W hW I hEI N]
      exact congrArg (fun T => (positiveDegreeSubspace F W hW N).map
        (furtherPositiveLinearMap F W hW I hEI) ⊔ T) ih

theorem idealPositiveDegreeGrowth_le_original (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (I : TwoSidedIdeal (WordAlgebra F))
    (hEI : allCutTwoSidedIdeal F W hW ≤ I) (N : ℕ) :
    idealPositiveDegreeGrowth F I N ≤ positiveDegreeGrowth F W hW N := by
  unfold idealPositiveDegreeGrowth
  rw [idealPositiveFiltration_eq_map F W hW I hEI N]
  exact Submodule.finrank_map_le (furtherPositiveLinearMap F W hW I hEI)
    (positiveDegreeFiltration F W hW N)

theorem furtherQuotient_upper_exponents (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (I : TwoSidedIdeal (WordAlgebra F))
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I) (ε : ℝ) (hε : 0 < ε) :
    2 + ε ∈ CriticalGK2.Growth.UpperExponentSet (idealPositiveDegreeGrowth F I) := by
  obtain ⟨C, hC, hu⟩ := sparseDegreeGrowth_near_two_upper F Λ hΛ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  have h : idealPositiveDegreeGrowth F I n ≤ sparseDegreeGrowth F Λ hΛ n :=
    idealPositiveDegreeGrowth_le_original F _ _ I hEI n
  have hr : (idealPositiveDegreeGrowth F I n : ℝ) ≤ (sparseDegreeGrowth F Λ hΛ n : ℝ) := by
    exact_mod_cast h
  exact hr.trans (hu n hn)

theorem furtherQuotient_logarithmic_limit (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (I : TwoSidedIdeal (WordAlgebra F))
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I)
    (hhom : WordIdealHomogeneous F I) (htail : NoWordTail F I) :
    Tendsto (CriticalGK2.Growth.logarithmicGrowthRatio (idealPositiveDegreeGrowth F I))
      atTop (𝓝 2) := by
  apply CriticalGK2.Growth.tendsto_logarithmicGrowthRatio_two
  · intro n _
    have h := sparse_furtherQuotient_growth_quadratic_lower F Λ hΛ I hEI hhom htail n
    have hs : n ^ 2 ≤ n * (n + 3) := by
      rw [Nat.pow_two]
      exact Nat.mul_le_mul_left n (Nat.le_add_right n 3)
    exact_mod_cast hs.trans h
  · exact furtherQuotient_upper_exponents F Λ hΛ I hEI

theorem furtherQuotient_envelope_upper (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (hmono : Monotone Λ) (hone : ∀ n : ℕ, 0 < n → 1 ≤ Λ n)
    (I : TwoSidedIdeal (WordAlgebra F))
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I) (n : ℕ) (hn : 0 < n) :
    (idealPositiveDegreeGrowth F I n : ℝ) ≤ 4 * ((n : ℝ) + 1) ^ 2 * Λ n := by
  have h : idealPositiveDegreeGrowth F I n ≤ sparseDegreeGrowth F Λ hΛ n :=
    idealPositiveDegreeGrowth_le_original F _ _ I hEI n
  have hr : (idealPositiveDegreeGrowth F I n : ℝ) ≤ (sparseDegreeGrowth F Λ hΛ n : ℝ) := by
    exact_mod_cast h
  exact hr.trans (sparseDegreeGrowth_envelope_upper F Λ hΛ hmono hone n hn)

#print axioms CriticalGK2.Actual.idealPositiveDegreeGrowth_le_original
#print axioms CriticalGK2.Actual.furtherQuotient_logarithmic_limit
#print axioms CriticalGK2.Actual.furtherQuotient_envelope_upper

end

end CriticalGK2.Actual
