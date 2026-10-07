import CriticalGK2.ActualCutDimension
import CriticalGK2.PositiveComponents

/-!
# Actual finite degree filtrations in the positive quotient

The filtration is the finite sum of the images of the actual homogeneous
quotients in the actual non-unital algebra. Its growth function is the actual
finrank of that submodule. The ambient algebra is allowed to be infinite
dimensional; finite dimensionality is proved only for the finite filtration.
The cut dimension inequality is then summed for this growth function.
-/

namespace CriticalGK2.Actual

noncomputable section

open scoped BigOperators

variable (F : Type*) [Field F]

/-- The actual image of positive degree m+1 in A. -/
def positiveDegreeSubspace (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (m : ℕ) : Submodule F (PositiveAllCutQuotient F W hW) :=
  LinearMap.range (componentQuotientToPositive F W hW (m + 1) (by omega))

instance positiveDegreeSubspace_finite (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (m : ℕ) :
    FiniteDimensional F (positiveDegreeSubspace F W hW m) := by
  letI : FiniteDimensional F (homogeneous F (m + 1)) :=
    (homogeneousWordBasis F (m + 1)).finiteDimensional_of_finite
  letI : FiniteDimensional F (ComponentQuotient F W (m + 1)) := inferInstance
  exact Module.Finite.range (componentQuotientToPositive F W hW (m + 1) (by omega))

/-- Injectivity of the actual component map identifies its image dimension. -/
theorem positiveDegreeSubspace_finrank (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (m : ℕ) :
    Module.finrank F (positiveDegreeSubspace F W hW m) =
      Module.finrank F (ComponentQuotient F W (m + 1)) :=
  LinearMap.finrank_range_of_inj
    (componentQuotientToPositive_injective F W hW (m + 1) (by omega))

/-- The degree-N filtration in the actual positive quotient. -/
def positiveDegreeFiltration (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (N : ℕ) : Submodule F (PositiveAllCutQuotient F W hW) :=
  (Finset.range N).sup (positiveDegreeSubspace F W hW)

instance positiveDegreeFiltration_finite (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    FiniteDimensional F (positiveDegreeFiltration F W hW N) := by
  unfold positiveDegreeFiltration
  infer_instance

/-- The actual finite degree growth function. -/
def positiveDegreeGrowth (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (N : ℕ) : ℕ := Module.finrank F (positiveDegreeFiltration F W hW N)

/-- Increasing the actual degree cutoff enlarges the actual filtration. -/
theorem positiveDegreeFiltration_mono (W : DyadicDualData F)
    (hW : PrimalCoherent F W) : Monotone (positiveDegreeFiltration F W hW) := by
  intro N M hNM
  apply Finset.sup_mono
  intro i hi
  exact Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hNM)

/-- An actual homogeneous element is in the actual filtration as soon as
its degree is allowed. -/
theorem homogeneousToPositiveQuotient_mem_filtration (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (m N : ℕ) (hm : m < N)
    (x : homogeneous F (m + 1)) :
    homogeneousToPositiveQuotient F W hW (m + 1) (by omega) x ∈
      positiveDegreeFiltration F W hW N := by
  have hle : positiveDegreeSubspace F W hW m ≤ positiveDegreeFiltration F W hW N :=
    Finset.le_sup (Finset.mem_range.mpr hm)
  exact hle ⟨Submodule.Quotient.mk x, rfl⟩

/-- Monotonicity is also true for the actual finite dimensions. -/
theorem positiveDegreeGrowth_mono (W : DyadicDualData F)
    (hW : PrimalCoherent F W) : Monotone (positiveDegreeGrowth F W hW) := by
  intro N M hNM
  exact Submodule.finrank_mono (positiveDegreeFiltration_mono F W hW hNM)

@[simp]
theorem positiveDegreeGrowth_zero (W : DyadicDualData F)
    (hW : PrimalCoherent F W) : positiveDegreeGrowth F W hW 0 = 0 := by
  unfold positiveDegreeGrowth positiveDegreeFiltration
  rw [Finset.range_zero, Finset.sup_empty]
  exact finrank_bot _ _

/-- A finite sum of finite subspaces is bounded without imposing finite
dimensionality on the whole ambient vector space. -/
theorem finite_subspace_finrank_sup_le_sum {ι X : Type*}
    [AddCommGroup X] [Module F X] (S : ι → Submodule F X)
    [∀ i, FiniteDimensional F (S i)] (t : Finset ι) :
    Module.finrank F ↥(t.sup S) ≤ ∑ i ∈ t, Module.finrank F (S i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      rw [Finset.sup_insert, Finset.sum_insert hi]
      exact (Submodule.finrank_add_le_finrank_add_finrank (S i) (t.sup S)).trans
        (Nat.add_le_add_left ih (Module.finrank F (S i)))

/-- The actual filtration growth is bounded by the sum of actual component
dimensions. -/
theorem positiveDegreeGrowth_le_component_sum (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    positiveDegreeGrowth F W hW N ≤
      ∑ m ∈ Finset.range N, Module.finrank F (ComponentQuotient F W (m + 1)) := by
  have h := finite_subspace_finrank_sup_le_sum F
    (positiveDegreeSubspace F W hW) (Finset.range N)
  simpa only [positiveDegreeGrowth, positiveDegreeFiltration,
    positiveDegreeSubspace_finrank] using h

/-- The full cut sum bounds the actual finite degree growth. -/
theorem positiveDegreeGrowth_le_cut_sum (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    positiveDegreeGrowth F W hW N ≤
      ∑ m ∈ Finset.range N, ∑ i : Fin (m + 2),
        Module.finrank F ((homogeneousLeftCompletion F W i.val).dualAnnihilator) *
        Module.finrank F ((homogeneousRightCompletion F W (m + 1 - i.val)).dualAnnihilator) := by
  exact (positiveDegreeGrowth_le_component_sum F W hW N).trans
    (Finset.sum_le_sum fun m _ => componentQuotient_finrank_le_cut_sum F W (m + 1))

/-- A contraction budget for the completion spaces gives an upper bound
on the degree-filtration growth function. -/
theorem positiveDegreeGrowth_le_uniform_cut_budget (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N B : ℕ)
    (hleft : ∀ m ∈ Finset.range N, ∀ i : Fin (m + 2),
      Module.finrank F ((homogeneousLeftCompletion F W i.val).dualAnnihilator) ≤ B)
    (hright : ∀ m ∈ Finset.range N, ∀ i : Fin (m + 2),
      Module.finrank F ((homogeneousRightCompletion F W (m + 1 - i.val)).dualAnnihilator) ≤ B) :
    positiveDegreeGrowth F W hW N ≤ N * (N + 1) * B ^ 2 := by
  calc
    positiveDegreeGrowth F W hW N ≤
        ∑ m ∈ Finset.range N, Module.finrank F (ComponentQuotient F W (m + 1)) :=
      positiveDegreeGrowth_le_component_sum F W hW N
    _ ≤ ∑ m ∈ Finset.range N, (m + 2) * B ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact componentQuotient_finrank_le_uniform_cut_budget F W (m + 1) B
        (hleft m hm) (hright m hm)
    _ ≤ ∑ _m ∈ Finset.range N, (N + 1) * B ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      have hm' := Finset.mem_range.mp hm
      exact Nat.mul_le_mul_right (B ^ 2) (by omega)
    _ = N * (N + 1) * B ^ 2 := by simp [Nat.mul_assoc]

#print axioms CriticalGK2.Actual.positiveDegreeSubspace_finrank
#print axioms CriticalGK2.Actual.positiveDegreeGrowth_le_cut_sum
#print axioms CriticalGK2.Actual.positiveDegreeGrowth_le_uniform_cut_budget

end

end CriticalGK2.Actual
