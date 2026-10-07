import CriticalGK2.PositiveGrowthFiltration
import CriticalGK2.GradedSurvival

/-!
# Actual finite homogeneous sums and the exact growth dimension

A finite family of actual component quotients maps into the actual positive
algebra by adding their actual images. The map is injective because a relation
can be lifted to the original free algebra and projected to each degree.
The resulting dimension formula gives the exact finite degree growth
identity.
-/

namespace CriticalGK2.Actual

noncomputable section

open scoped BigOperators

variable (F : Type*) [Field F]

/-- The literal sum of actual component quotient maps into A. -/
def positiveFiniteDegreeSumMap (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (N : ℕ) : (∀ i : Fin N, ComponentQuotient F W (i.val + 1)) →ₗ[F]
      PositiveAllCutQuotient F W hW where
  toFun x := ∑ i, componentQuotientToPositive F W hW (i.val + 1) (by omega) (x i)
  map_add' x y := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

/-- A literal finite homogeneous relation in the actual quotient has every
component zero. -/
theorem positiveFiniteDegreeSumMap_eq_zero_iff (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ)
    (x : ∀ i : Fin N, ComponentQuotient F W (i.val + 1)) :
    positiveFiniteDegreeSumMap F W hW N x = 0 ↔ x = 0 := by
  classical
  constructor
  · intro hzero
    choose y hy using fun i : Fin N => Submodule.Quotient.mk_surjective
      ((allCutComponent F W (i.val + 1)).comap (homogeneous F (i.val + 1)).subtype) (x i)
    have hmaps : ∀ i : Fin N,
        componentQuotientToPositive F W hW (i.val + 1) (by omega) (x i) =
          homogeneousToPositiveQuotient F W hW (i.val + 1) (by omega) (y i) := by
      intro i
      rw [← hy i, componentQuotientToPositive_mk]
    have hsumA : (∑ i : Fin N,
        homogeneousToPositiveQuotient F W hW (i.val + 1) (by omega) (y i)) = 0 := by
      change (∑ i : Fin N,
        componentQuotientToPositive F W hW (i.val + 1) (by omega) (x i)) = 0 at hzero
      simpa only [hmaps] using hzero
    have hsumB : (∑ i : Fin N, allCutQuotientMap F W hW (y i).val) = 0 := by
      have h := congrArg (positiveQuotientLinearInclusion F W hW) hsumA
      simpa only [map_sum, map_zero, positiveQuotientLinearInclusion,
        homogeneousToPositiveQuotient_val] using h
    have hE : (∑ i : Fin N, (y i).val) ∈ allCutSubmodule F W := by
      apply (allCutQuotientMap_eq_zero_iff F W hW _).mp
      simpa only [map_sum] using hsumB
    funext i
    let p : WordAlgebra F →ₗ[F] WordAlgebra F :=
      (homogeneous F (i.val + 1)).subtype.comp (homogeneousProjection F (i.val + 1))
    have hp : ∀ j : Fin N, p (y j).val = if j = i then (y i).val else 0 := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [p, LinearMap.comp_apply, Submodule.subtype_apply,
          homogeneousProjection_of_mem F (i.val + 1) (y i).val (y i).property, ite_true]
      · have hdegree : j.val + 1 ≠ i.val + 1 := by
          intro h
          apply hji
          apply Fin.ext
          omega
        simp only [p, LinearMap.comp_apply, Submodule.subtype_apply,
          homogeneousProjection_of_other_degree F (j.val + 1) (i.val + 1)
            hdegree (y j).val (y j).property, if_neg hji]
    have hproject : (homogeneousProjection F (i.val + 1)
        (∑ j : Fin N, (y j).val)).val = (y i).val := by
      change p (∑ j : Fin N, (y j).val) = _
      simp only [map_sum, hp]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · intro hnot
        exact (hnot (Finset.mem_univ i)).elim
    have hcomponent := homogeneousProjection_allCutSubmodule_mem F W (i.val + 1) _ hE
    rw [hproject] at hcomponent
    rw [← hy i]
    exact (Submodule.Quotient.mk_eq_zero
      ((allCutComponent F W (i.val + 1)).comap (homogeneous F (i.val + 1)).subtype)).mpr
        hcomponent
  · intro hzero
    rw [hzero, map_zero]

/-- The actual finite sum map is injective, including N=0. -/
theorem positiveFiniteDegreeSumMap_injective (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    Function.Injective (positiveFiniteDegreeSumMap F W hW N) := by
  intro x y hxy
  have hzero : positiveFiniteDegreeSumMap F W hW N (x - y) = 0 := by
    calc
      positiveFiniteDegreeSumMap F W hW N (x - y) =
          positiveFiniteDegreeSumMap F W hW N x - positiveFiniteDegreeSumMap F W hW N y :=
        (positiveFiniteDegreeSumMap F W hW N).map_sub x y
      _ = 0 := sub_eq_zero.mpr hxy
  exact sub_eq_zero.mp ((positiveFiniteDegreeSumMap_eq_zero_iff F W hW N (x - y)).mp hzero)

/-- Its actual range is inside the actual finite degree filtration. -/
theorem positiveFiniteDegreeSumMap_range_le_filtration (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    LinearMap.range (positiveFiniteDegreeSumMap F W hW N) ≤
      positiveDegreeFiltration F W hW N := by
  classical
  rintro a ⟨x, rfl⟩
  change (∑ i : Fin N,
    componentQuotientToPositive F W hW (i.val + 1) (by omega) (x i)) ∈ _
  apply Submodule.sum_mem
  intro i _
  have hle : positiveDegreeSubspace F W hW i.val ≤ positiveDegreeFiltration F W hW N :=
    Finset.le_sup (Finset.mem_range.mpr i.isLt)
  exact hle ⟨x i, rfl⟩

/-- Actual finite homogeneous independence gives the reverse dimension
inequality for the actual degree filtration. -/
theorem component_sum_le_positiveDegreeGrowth (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    (∑ i : Fin N, Module.finrank F (ComponentQuotient F W (i.val + 1))) ≤
      positiveDegreeGrowth F W hW N := by
  letI : ∀ i : Fin N, FiniteDimensional F (ComponentQuotient F W (i.val + 1)) := fun i => by
    letI : FiniteDimensional F (homogeneous F (i.val + 1)) :=
      (homogeneousWordBasis F (i.val + 1)).finiteDimensional_of_finite
    infer_instance
  letI : ∀ i : Fin N, Module.Free F (ComponentQuotient F W (i.val + 1)) := fun i =>
    Module.Free.of_basis (Module.Basis.ofVectorSpace F (ComponentQuotient F W (i.val + 1)))
  calc
    (∑ i : Fin N, Module.finrank F (ComponentQuotient F W (i.val + 1))) =
        Module.finrank F (∀ i : Fin N, ComponentQuotient F W (i.val + 1)) :=
      (Module.finrank_pi_fintype F).symm
    _ = Module.finrank F (LinearMap.range (positiveFiniteDegreeSumMap F W hW N)) :=
      (LinearMap.finrank_range_of_inj (positiveFiniteDegreeSumMap_injective F W hW N)).symm
    _ ≤ positiveDegreeGrowth F W hW N :=
      Submodule.finrank_mono (positiveFiniteDegreeSumMap_range_le_filtration F W hW N)

/-- Exact growth identity for the actual finite degree submodule. -/
theorem positiveDegreeGrowth_eq_component_sum (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    positiveDegreeGrowth F W hW N =
      ∑ m ∈ Finset.range N, Module.finrank F (ComponentQuotient F W (m + 1)) := by
  apply Nat.le_antisymm (positiveDegreeGrowth_le_component_sum F W hW N)
  have hs : (∑ i : Fin N, Module.finrank F (ComponentQuotient F W (i.val + 1))) =
      ∑ m ∈ Finset.range N, Module.finrank F (ComponentQuotient F W (m + 1)) :=
    Fin.sum_univ_eq_sum_range (fun m : ℕ => Module.finrank F (ComponentQuotient F W (m + 1))) N
  rw [← hs]
  exact component_sum_le_positiveDegreeGrowth F W hW N

/-- Sum of the linear per-degree lower bounds, written without division. -/
theorem twice_sum_linear_degrees (N : ℕ) :
    2 * (∑ m ∈ Finset.range N, (m + 2)) = N * (N + 3) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      ring

/-- Any proved actual linear component lower bound gives the quadratic
lower bound for the actual finite degree growth. -/
theorem positiveDegreeGrowth_quadratic_lower_of_components (W : DyadicDualData F)
    (hW : PrimalCoherent F W)
    (hlower : ∀ m : ℕ, m + 2 ≤ Module.finrank F (ComponentQuotient F W (m + 1)))
    (N : ℕ) : N * (N + 3) ≤ 2 * positiveDegreeGrowth F W hW N := by
  rw [positiveDegreeGrowth_eq_component_sum]
  have hsum : (∑ m ∈ Finset.range N, (m + 2)) ≤
      ∑ m ∈ Finset.range N, Module.finrank F (ComponentQuotient F W (m + 1)) :=
    Finset.sum_le_sum fun m _ => hlower m
  rw [← twice_sum_linear_degrees N]
  exact Nat.mul_le_mul_left 2 hsum

#print axioms CriticalGK2.Actual.positiveFiniteDegreeSumMap_injective
#print axioms CriticalGK2.Actual.component_sum_le_positiveDegreeGrowth
#print axioms CriticalGK2.Actual.positiveDegreeGrowth_eq_component_sum

end

end CriticalGK2.Actual
