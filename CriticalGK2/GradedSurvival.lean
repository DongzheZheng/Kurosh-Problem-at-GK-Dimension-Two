import CriticalGK2.PositiveComponents
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Positive homogeneous survival implies actual infinite dimension

A finite relation among representatives in distinct positive degrees can be
projected to each degree in the original free algebra. The exact same-degree
ideal intersection then shows that every coefficient vanishes in the actual
quotient. These independent representatives give infinite-dimensionality.
-/

namespace CriticalGK2.Actual

open scoped BigOperators

noncomputable section

variable (F : Type*) [Field F]

def positiveQuotientLinearInclusion (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    PositiveAllCutQuotient F W hW →ₗ[F] AllCutRingQuotient F W hW where
  toFun a := a.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem homogeneous_quotient_linearlyIndependent
    (W : DyadicDualData F) (hW : PrimalCoherent F W) (x : ℕ → WordAlgebra F)
    (hx : ∀ n, x n ∈ homogeneous F (n + 1))
    (hne : ∀ n, allCutQuotientMap F W hW (x n) ≠ 0) :
    LinearIndependent F (fun n => allCutQuotientMap F W hW (x n)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s g hsum i hi
  have hE : (∑ j ∈ s, g j • x j) ∈ allCutSubmodule F W := by
    apply (allCutQuotientMap_eq_zero_iff F W hW _).mp
    simpa only [map_sum, allCutQuotientMap_smul] using hsum
  let p : WordAlgebra F →ₗ[F] WordAlgebra F :=
    (homogeneous F (i + 1)).subtype.comp (homogeneousProjection F (i + 1))
  have hp : ∀ j, p (x j) = if j = i then x j else 0 := by
    intro j
    by_cases he : j = i
    · subst j
      simp only [p, LinearMap.comp_apply, Submodule.subtype_apply,
        homogeneousProjection_of_mem F (i + 1) (x i) (hx i), ite_true]
    · have hdeg : j + 1 ≠ i + 1 := by omega
      simp only [p, LinearMap.comp_apply, Submodule.subtype_apply,
        homogeneousProjection_of_other_degree F (j + 1) (i + 1) hdeg (x j) (hx j), if_neg he]
  have hprojection : (homogeneousProjection F (i + 1) (∑ j ∈ s, g j • x j)).val =
      g i • x i := by
    change p (∑ j ∈ s, g j • x j) = _
    simp only [map_sum, map_smul, hp]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hn
      exact (hn hi).elim
  have hcomponent := homogeneousProjection_allCutSubmodule_mem F W (i + 1) _ hE
  rw [hprojection] at hcomponent
  have hzero := (allCutQuotientMap_eq_zero_iff F W hW (g i • x i)).mpr
    (allCutComponent_le_allCutSubmodule F W (i + 1) hcomponent)
  rw [allCutQuotientMap_smul] at hzero
  exact (smul_eq_zero.mp hzero).resolve_right (hne i)

/-- All actual dual roots survive, so the actual positive algebra has an
infinite linearly independent family and is not a finite module over F. -/
theorem positiveAllCutQuotient_not_finite (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (hne : ∀ h, W h ≠ ⊥) :
    ¬ Module.Finite F (PositiveAllCutQuotient F W hW) := by
  classical
  choose x hx hxne using fun n : ℕ => exists_homogeneous_quotient_ne_zero F W hW
    (n + 1) (by omega) (hne (strictDyadicRoot (n + 1)))
  let a : ℕ → PositiveAllCutQuotient F W hW := fun n =>
    homogeneousToPositiveQuotient F W hW (n + 1) (by omega) ⟨x n, hx n⟩
  have hlinear : LinearIndependent F a := by
    apply LinearIndependent.of_comp (positiveQuotientLinearInclusion F W hW)
    exact homogeneous_quotient_linearlyIndependent F W hW x hx hxne
  intro hfinite
  letI := hfinite
  exact Module.Finite.not_linearIndependent_of_infinite a hlinear

#print axioms CriticalGK2.Actual.positiveAllCutQuotient_not_finite

end

end CriticalGK2.Actual
