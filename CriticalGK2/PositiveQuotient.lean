import CriticalGK2.AllCutIdeal
import CriticalGK2.HomogeneousProjection
import CriticalGK2.WordSurvival
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra

/-!
# The actual positive, non-unital all-cut quotient

`AllCutRingQuotient` is the unital algebra B = H/E.  This file proves that E
is contained in the actual augmentation kernel and descends that augmentation
to B.  The actual non-unital algebra A is its kernel, with the operations and
scalar structures inherited from an actual `NonUnitalSubalgebra` of B.

The equality with the image of the original positive part, and the positive
homogeneous survival statements, are proved from the existing actual ideal and
projection theorems.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- The augmentation is the actual coefficient of the empty word. -/
theorem augmentation_eq_constantCoeff (x : WordAlgebra F) :
    augmentation F x = x 1 := by
  classical
  induction x using Finsupp.induction with
  | zero =>
      change augmentation F (0 : WordAlgebra F) = (0 : F)
      exact map_zero _
  | single_add w c a hwa hc ih =>
      change augmentation F (MonoidAlgebra.single w c + MonoidAlgebra.ofCoeff a) =
        (MonoidAlgebra.single w c) 1 + (MonoidAlgebra.ofCoeff a) 1
      have ih' : augmentation F (MonoidAlgebra.ofCoeff a) =
          (MonoidAlgebra.ofCoeff a) 1 := ih
      rw [map_add, ih']
      congr 1
      rw [augmentation_monomial]
      by_cases hw : w = 1
      · subst w
        simp [MonoidAlgebra.single]
      · have hwlen : w.length ≠ 0 := fun h => hw (FreeMonoid.length_eq_zero.mp h)
        simp [hwlen, MonoidAlgebra.single, Finsupp.single_apply, hw]

theorem augmentation_homogeneous_eq_zero (n : ℕ) (hn : n ≠ 0)
    (x : WordAlgebra F) (hx : x ∈ homogeneous F n) : augmentation F x = 0 := by
  rw [augmentation_eq_constantCoeff]
  exact (mem_homogeneous_iff F n x).mp hx 1 (by simpa using Ne.symm hn)

/-- The original positive part as an actual F-submodule of H. -/
def positiveWordSubmodule : Submodule F (WordAlgebra F) :=
  (augmentation F).toLinearMap.ker

@[simp]
theorem mem_positiveWordSubmodule (x : WordAlgebra F) :
    x ∈ positiveWordSubmodule F ↔ augmentation F x = 0 := Iff.rfl

theorem allCutSubmodule_le_positiveWordSubmodule (W : DyadicDualData F) :
    allCutSubmodule F W ≤ positiveWordSubmodule F := by
  apply iSup_le
  intro n x hx
  exact augmentation_homogeneous_eq_zero F (n + 1) (by omega) x
    (allCutComponent_le_homogeneous F W (n + 1) hx)

/-- The actual all-cut ideal is contained in the actual augmentation ideal. -/
theorem allCutTwoSidedIdeal_le_augmentationIdeal (W : DyadicDualData F)
    (hW : PrimalCoherent F W) :
    allCutTwoSidedIdeal F W hW ≤ augmentationIdeal F := by
  intro x hx
  change augmentation F x = 0
  exact allCutSubmodule_le_positiveWordSubmodule F W
    ((mem_allCutTwoSidedIdeal F W hW x).mp hx)

/-- Actual algebra quotient map H -> B, with Mathlib's quotient algebra structure. -/
def allCutQuotientMap (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    WordAlgebra F →ₐ[F] AllCutRingQuotient F W hW :=
  (allCutTwoSidedIdeal F W hW).ringCon.mkₐ F

theorem allCutQuotientMap_surjective (W : DyadicDualData F)
    (hW : PrimalCoherent F W) : Function.Surjective (allCutQuotientMap F W hW) :=
  RingCon.mkₐ_surjective _

@[simp]
theorem allCutQuotientMap_smul (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (c : F) (x : WordAlgebra F) :
    allCutQuotientMap F W hW (c • x) = c • allCutQuotientMap F W hW x :=
  map_smul _ c x

@[simp]
theorem allCutQuotientMap_eq_zero_iff (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (x : WordAlgebra F) :
    allCutQuotientMap F W hW x = 0 ↔ x ∈ allCutSubmodule F W := by
  change (allCutTwoSidedIdeal F W hW).ringCon.mk' x = 0 ↔
    x ∈ allCutSubmodule F W
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk',
    mem_allCutTwoSidedIdeal]

theorem allCut_congruence_le_augmentation_ker (W : DyadicDualData F)
    (hW : PrimalCoherent F W) :
    (allCutTwoSidedIdeal F W hW).ringCon ≤ RingCon.ker (augmentation F).toRingHom := by
  intro x y hxy
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply allCutSubmodule_le_positiveWordSubmodule F W
  exact (mem_allCutTwoSidedIdeal F W hW (x - y)).mp
    (((allCutTwoSidedIdeal F W hW).rel_iff x y).mp hxy)

/-- The actual scalar augmentation B -> F. -/
def allCutQuotientAugmentation (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    AllCutRingQuotient F W hW →ₐ[F] F :=
  (allCutTwoSidedIdeal F W hW).ringCon.liftₐ (augmentation F)
    (allCut_congruence_le_augmentation_ker F W hW)

@[simp]
theorem allCutQuotientAugmentation_map (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (x : WordAlgebra F) :
    allCutQuotientAugmentation F W hW (allCutQuotientMap F W hW x) =
      augmentation F x := rfl

/-- The actual positive subalgebra A inside B. -/
def positiveAllCutSubalgebra (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    NonUnitalSubalgebra F (AllCutRingQuotient F W hW) :=
  ((allCutQuotientAugmentation F W hW).toLinearMap.ker).toNonUnitalSubalgebra
    (fun x y hx hy => by
      change allCutQuotientAugmentation F W hW (x * y) = 0
      change allCutQuotientAugmentation F W hW x = 0 at hx
      rw [map_mul, hx, zero_mul])

/-- A = H_+/E is realized as an actual kernel subtype of B = H/E. -/
def PositiveAllCutQuotient (W : DyadicDualData F) (hW : PrimalCoherent F W) : Type _ :=
  ↥(positiveAllCutSubalgebra F W hW)

/- The named positive algebra carries the standard inherited subalgebra
structures. -/

instance positiveAllCutQuotientNonUnitalRing (W : DyadicDualData F)
    (hW : PrimalCoherent F W) : NonUnitalRing (PositiveAllCutQuotient F W hW) :=
  NonUnitalSubalgebra.toNonUnitalRing (positiveAllCutSubalgebra F W hW)

instance positiveAllCutQuotientModule (W : DyadicDualData F)
    (hW : PrimalCoherent F W) : Module F (PositiveAllCutQuotient F W hW) :=
  NonUnitalSubalgebra.instModule (S := positiveAllCutSubalgebra F W hW)

instance positiveAllCutQuotientScalarTower (W : DyadicDualData F)
    (hW : PrimalCoherent F W) :
    IsScalarTower F (PositiveAllCutQuotient F W hW) (PositiveAllCutQuotient F W hW) where
  smul_assoc c x y := Subtype.ext (smul_mul_assoc c x.val y.val)

instance positiveAllCutQuotientSMulComm (W : DyadicDualData F)
    (hW : PrimalCoherent F W) :
    SMulCommClass F (PositiveAllCutQuotient F W hW) (PositiveAllCutQuotient F W hW) where
  smul_comm c x y := Subtype.ext (mul_smul_comm c x.val y.val).symm

@[simp]
theorem mem_positiveAllCutSubalgebra (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (x : AllCutRingQuotient F W hW) :
    x ∈ positiveAllCutSubalgebra F W hW ↔
      allCutQuotientAugmentation F W hW x = 0 := Iff.rfl

/-- The kernel definition agrees with the actual image of the positive part. -/
theorem positiveAllCutSubalgebra_eq_positive_image (W : DyadicDualData F)
    (hW : PrimalCoherent F W) :
    (positiveAllCutSubalgebra F W hW).toSubmodule =
      (positiveWordSubmodule F).map (allCutQuotientMap F W hW).toLinearMap := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := allCutQuotientMap_surjective F W hW x
    apply Submodule.mem_map.mpr
    refine ⟨a, ?_, rfl⟩
    change augmentation F a = 0
    exact hx
  · rintro ⟨a, ha, rfl⟩
    change augmentation F a = 0
    exact ha

/-- The original positive-part quotient map into the actual non-unital A. -/
def positiveAllCutQuotientMap (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    positiveWordSubmodule F →ₗ[F] PositiveAllCutQuotient F W hW where
  toFun x := ⟨allCutQuotientMap F W hW x.val, x.property⟩
  map_add' x y := Subtype.ext ((allCutQuotientMap F W hW).map_add x.val y.val)
  map_smul' c x := Subtype.ext ((allCutQuotientMap F W hW).toLinearMap.map_smul c x.val)

theorem positiveAllCutQuotientMap_surjective (W : DyadicDualData F)
    (hW : PrimalCoherent F W) :
    Function.Surjective (positiveAllCutQuotientMap F W hW) := by
  intro x
  obtain ⟨a, ha⟩ := allCutQuotientMap_surjective F W hW x.val
  have hapos : a ∈ positiveWordSubmodule F := by
    change augmentation F a = 0
    rw [← allCutQuotientAugmentation_map F W hW, ha]
    exact x.property
  exact ⟨⟨a, hapos⟩, Subtype.ext ha⟩

/-- The actual positive map has precisely E as its kernel. -/
theorem positiveAllCutQuotientMap_ker (W : DyadicDualData F)
    (hW : PrimalCoherent F W) :
    (positiveAllCutQuotientMap F W hW).ker =
      (allCutSubmodule F W).comap (positiveWordSubmodule F).subtype := by
  apply Submodule.ext
  intro x
  change positiveAllCutQuotientMap F W hW x = 0 ↔ x.val ∈ allCutSubmodule F W
  rw [← allCutQuotientMap_eq_zero_iff F W hW x.val]
  exact Subtype.ext_iff

/-- Every positive homogeneous degree contains an element surviving in B. -/
theorem exists_homogeneous_quotient_ne_zero (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : n ≠ 0)
    (hWroot : W (strictDyadicRoot n) ≠ ⊥) :
    ∃ x : WordAlgebra F, x ∈ homogeneous F n ∧ allCutQuotientMap F W hW x ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply allCutComponent_ne_homogeneous F W n hn hWroot
  apply le_antisymm (allCutComponent_le_homogeneous F W n)
  intro x hx
  have hE := (allCutQuotientMap_eq_zero_iff F W hW x).mp (h x hx)
  have hboth : x ∈ allCutSubmodule F W ⊓ homogeneous F n := ⟨hE, hx⟩
  rwa [allCutSubmodule_inf_homogeneous] at hboth

/-- The surviving positive homogeneous elements belong to the actual A. -/
theorem exists_positive_homogeneous_ne_zero (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : n ≠ 0)
    (hWroot : W (strictDyadicRoot n) ≠ ⊥) :
    ∃ a : PositiveAllCutQuotient F W hW, a ≠ 0 ∧
      ∃ x : WordAlgebra F, x ∈ homogeneous F n ∧
        allCutQuotientMap F W hW x = a.val := by
  obtain ⟨x, hx, hxne⟩ := exists_homogeneous_quotient_ne_zero F W hW n hn hWroot
  have hxpos := augmentation_homogeneous_eq_zero F n hn x hx
  refine ⟨⟨allCutQuotientMap F W hW x, hxpos⟩, ?_, x, hx, rfl⟩
  intro ha
  exact hxne (congrArg Subtype.val ha)

end

end CriticalGK2.Actual
