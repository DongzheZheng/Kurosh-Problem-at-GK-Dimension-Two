import CriticalGK2.PositiveQuotient
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Actual vector quotients and homogeneous components inside the positive algebra

The positive quotient vector space H_+/E is linearly isomorphic to the actual
non-unital algebra A defined in `PositiveQuotient`.  For every positive degree,
the actual homogeneous quotient H_n/E_n injects linearly into A.  The exact
kernel computation uses E intersect H_n = E_n, already proved for the actual
coefficient-filter projections.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- The actual quotient vector space of the original positive part by E. -/
abbrev PositiveVectorQuotient (W : DyadicDualData F) :=
  positiveWordSubmodule F ⧸
    (allCutSubmodule F W).comap (positiveWordSubmodule F).subtype

/-- The actual positive vector quotient is the underlying module of A. -/
def positiveVectorQuotientEquiv (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    PositiveVectorQuotient F W ≃ₗ[F] PositiveAllCutQuotient F W hW := by
  change (positiveWordSubmodule F ⧸
    (allCutSubmodule F W).comap (positiveWordSubmodule F).subtype) ≃ₗ[F]
      PositiveAllCutQuotient F W hW
  rw [← positiveAllCutQuotientMap_ker F W hW]
  exact (positiveAllCutQuotientMap F W hW).quotKerEquivOfSurjective
    (positiveAllCutQuotientMap_surjective F W hW)

/-- Actual degree-n elements map linearly to the actual positive algebra A. -/
def homogeneousToPositiveQuotient (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : n ≠ 0) :
    homogeneous F n →ₗ[F] PositiveAllCutQuotient F W hW where
  toFun x := ⟨allCutQuotientMap F W hW x.val,
    augmentation_homogeneous_eq_zero F n hn x.val x.property⟩
  map_add' x y := Subtype.ext ((allCutQuotientMap F W hW).map_add x.val y.val)
  map_smul' c x := Subtype.ext ((allCutQuotientMap F W hW).toLinearMap.map_smul c x.val)

@[simp]
theorem homogeneousToPositiveQuotient_val (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : n ≠ 0) (x : homogeneous F n) :
    (homogeneousToPositiveQuotient F W hW n hn x).val =
      allCutQuotientMap F W hW x.val := rfl

/-- Its kernel is the actual same-degree all-cut component. -/
theorem homogeneousToPositiveQuotient_ker (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : n ≠ 0) :
    (homogeneousToPositiveQuotient F W hW n hn).ker =
      (allCutComponent F W n).comap (homogeneous F n).subtype := by
  rw [← allCutSubmodule_comap_homogeneous F W n]
  apply Submodule.ext
  intro x
  change homogeneousToPositiveQuotient F W hW n hn x = 0 ↔
    x.val ∈ allCutSubmodule F W
  rw [← allCutQuotientMap_eq_zero_iff F W hW x.val]
  exact Subtype.ext_iff

/-- The component vector quotient maps into A using its proved actual kernel. -/
def componentQuotientToPositive (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : n ≠ 0) :
    ComponentQuotient F W n →ₗ[F] PositiveAllCutQuotient F W hW :=
  ((allCutComponent F W n).comap (homogeneous F n).subtype).liftQ
    (homogeneousToPositiveQuotient F W hW n hn)
    (homogeneousToPositiveQuotient_ker F W hW n hn).ge

@[simp]
theorem componentQuotientToPositive_mk (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : n ≠ 0) (x : homogeneous F n) :
    componentQuotientToPositive F W hW n hn (Submodule.Quotient.mk x) =
      homogeneousToPositiveQuotient F W hW n hn x := rfl

/-- No extra relations occur upon passing from H_n/E_n to the actual A. -/
theorem componentQuotientToPositive_injective (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (componentQuotientToPositive F W hW n hn) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot
    ((allCutComponent F W n).comap (homogeneous F n).subtype)
    (homogeneousToPositiveQuotient F W hW n hn)
    (homogeneousToPositiveQuotient_ker F W hW n hn).ge
    (homogeneousToPositiveQuotient_ker F W hW n hn).le

theorem positiveAllCutQuotient_nontrivial (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : n ≠ 0)
    (hWroot : W (strictDyadicRoot n) ≠ ⊥) :
    Nontrivial (PositiveAllCutQuotient F W hW) := by
  obtain ⟨a, ha, _⟩ := exists_positive_homogeneous_ne_zero F W hW n hn hWroot
  exact ⟨⟨a, 0, ha⟩⟩

end

end CriticalGK2.Actual
