import CriticalGK2.ActualStemBudget
import CriticalGK2.TensorSupportDimension
import CriticalGK2.TensorProductCutSupport
import CriticalGK2.RootCutSupportBudget
import CriticalGK2.StagedSpaces

/-!
# Literal all-cut bounds for actual homogeneous dual spaces

This is a transparent mathematical predicate on actual subspaces and their
actual arbitrary-functional contraction supports. The actual common-stem
construction discharges the predicate from the computed polynomial budget,
including the final scalar-exterior cut. Root completion dimensions are
then follow from these contraction supports.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct CriticalGK2.ContractionBudget

variable (F : Type*) [Field F]

def actualDualSpaceCutMap (n a b : ℕ) (hab : a + b = n) :
    HomogeneousDual F n ≃ₗ[F] HomogeneousDual F a ⊗[F] HomogeneousDual F b :=
  (homogeneousDualDegreeCast F hab).symm ≪≫ₗ (homogeneousDualTensorConcat F a b).symm

def actualDualSpaceCut (n a b : ℕ) (hab : a + b = n)
    (W : Submodule F (HomogeneousDual F n)) :
    Submodule F (HomogeneousDual F a ⊗[F] HomogeneousDual F b) :=
  W.map (actualDualSpaceCutMap F n a b hab).toLinearMap

def ActualDualCutBound (n : ℕ) (W : Submodule F (HomogeneousDual F n)) (B : ℕ) : Prop :=
  ∀ a b : ℕ, ∀ hab : a + b = n,
    Module.finrank F (tensorPrefixSupport (actualDualSpaceCut F n a b hab W)) ≤ B ∧
    Module.finrank F (tensorSuffixSupport (actualDualSpaceCut F n a b hab W)) ≤ B

theorem actualDualSpaceCut_finrank (n a b : ℕ) (hab : a + b = n)
    (W : Submodule F (HomogeneousDual F n)) :
    Module.finrank F (actualDualSpaceCut F n a b hab W) = Module.finrank F W :=
  (actualDualSpaceCutMap F n a b hab).finrank_map_eq W

theorem actualDualCutBound_mono (n : ℕ) {S T : Submodule F (HomogeneousDual F n)}
    (hST : S ≤ T) (B : ℕ) (hT : ActualDualCutBound F n T B) : ActualDualCutBound F n S B := by
  classical
  intro a b hab
  letI : FiniteDimensional F (HomogeneousDual F a) :=
    (homogeneousWordBasis F a).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (HomogeneousDual F b) :=
    (homogeneousWordBasis F b).dualBasis.finiteDimensional_of_finite
  have hc : actualDualSpaceCut F n a b hab S ≤ actualDualSpaceCut F n a b hab T :=
    Submodule.map_mono hST
  exact ⟨(Submodule.finrank_mono (tensorPrefixSupport_mono hc)).trans (hT a b hab).1,
    (Submodule.finrank_mono (tensorSuffixSupport_mono hc)).trans (hT a b hab).2⟩

theorem actualDualCutBound_budget_mono (n : ℕ) (W : Submodule F (HomogeneousDual F n))
    {B C : ℕ} (hBC : B ≤ C) (hB : ActualDualCutBound F n W B) : ActualDualCutBound F n W C :=
  fun a b hab => ⟨(hB a b hab).1.trans hBC, (hB a b hab).2.trans hBC⟩

theorem actualDualCutBound_degreeCast {n m : ℕ} (h : n = m)
    (W : Submodule F (HomogeneousDual F n)) (B : ℕ) (hB : ActualDualCutBound F n W B) :
    ActualDualCutBound F m (W.map (homogeneousDualDegreeCast F h).toLinearMap) B := by
  subst m
  simpa only [homogeneousDualDegreeCast, LinearEquiv.refl_toLinearMap, Submodule.map_id] using hB

theorem actualDualSpaceCut_stem_inside (a b : ℕ) (P : WordAlgebra F) :
    actualDualSpaceCut F ((a + b) + 1) a (b + 1) (Nat.add_assoc a b 1).symm
      (actualStemDualSpace F (a + b) P) = actualStemInsideCutSpace F a b P := by
  change (actualStemDualSpace F (a + b) P).map
    ((homogeneousDualTensorConcat F a (b + 1)).symm.toLinearMap.comp
      (homogeneousDualDegreeCast F (Nat.add_assoc a b 1).symm).symm.toLinearMap) = _
  rw [homogeneousDualDegreeCast_symm_eq F (Nat.add_assoc a b 1), LinearEquiv.symm_symm]
  rfl

/-- Every literal cut of the actual common-stem space is controlled by
the computed 2*rho budget. The endpoint is proved using the true scalar
exterior and actual dimension two. -/
theorem actualStemDualSpace_cutBound (q : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F q) (hP0 : P ≠ 0) :
    ActualDualCutBound F (q + 1) (actualStemDualSpace F q P)
      (2 * polynomialCutBudget F q P) := by
  classical
  intro a b hab
  by_cases ha : a ≤ q
  · obtain ⟨c, hq⟩ := Nat.exists_eq_add_of_le ha
    have hb : b = c + 1 := by omega
    subst q
    subst b
    have hc : actualDualSpaceCut F ((a + c) + 1) a (c + 1) hab
        (actualStemDualSpace F (a + c) P) = actualStemInsideCutSpace F a c P :=
      actualDualSpaceCut_stem_inside F a c P
    rw [hc, actualStemInsideCut_prefixSupport_finrank, actualStemInsideCut_suffixSupport_finrank]
    have hr := (polynomialCutBudget_le_iff F (a + c) P _).mp le_rfl a c rfl
    constructor <;> omega
  · have ha0 : a = q + 1 := by omega
    have hb0 : b = 0 := by omega
    subst a
    subst b
    letI : FiniteDimensional F (HomogeneousDual F (q + 1)) :=
      (homogeneousWordBasis F (q + 1)).dualBasis.finiteDimensional_of_finite
    letI : FiniteDimensional F (HomogeneousDual F 0) :=
      (homogeneousWordBasis F 0).dualBasis.finiteDimensional_of_finite
    have hdim : Module.finrank F (actualDualSpaceCut F (q + 1) (q + 1) 0 hab
        (actualStemDualSpace F q P)) = 2 :=
      (actualDualSpaceCut_finrank F _ _ _ hab _).trans
        (actualStemDualSpace_finrank F q P hP hP0)
    have hzero : Module.finrank F (HomogeneousDual F 0) = 1 := by
      rw [← (coefficientSelfDual F 0).finrank_eq, finrank_homogeneous_zero]
    have hpos := polynomialCutBudget_pos F q P hP hP0
    constructor
    · calc
        _ ≤ Module.finrank F (actualDualSpaceCut F (q + 1) (q + 1) 0 hab
              (actualStemDualSpace F q P)) * Module.finrank F (HomogeneousDual F 0) :=
          tensorPrefixSupport_finrank_le _
        _ = 2 := by rw [hdim, hzero]
        _ ≤ 2 * polynomialCutBudget F q P := by omega
    · calc
        _ ≤ Module.finrank F (HomogeneousDual F 0) := by
          simpa only [finrank_top] using Submodule.finrank_mono
            (show tensorSuffixSupport (actualDualSpaceCut F (q + 1) (q + 1) 0 hab
              (actualStemDualSpace F q P)) ≤ ⊤ from le_top)
        _ = 1 := hzero
        _ ≤ 2 * polynomialCutBudget F q P := by omega

theorem prefixSpace_dualCoefficientSpace_eq_actualStemDualSpace
    (q : ℕ) (P : WordAlgebra F) (hP : WordHomogeneous q P) :
    dualCoefficientSpace F (q + 1) (prefixSpace F P) = actualStemDualSpace F q P := by
  let t : StemWord q → F := fun a => P (FreeMonoid.ofList (List.ofFn a))
  have hread : stemPolynomial F q t = P := stemPolynomial_of_coefficients F q P hP
  have h := stemSpace_dualCoefficientSpace_eq_actualStemDualSpace F q t
  rw [stemSpace_eq_prefixSpace, hread] at h
  exact h

theorem actualStemCutBudget_le_of_cutBound (q : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F q) (hP0 : P ≠ 0) (B : ℕ)
    (hB : ActualDualCutBound F (q + 1) (actualStemDualSpace F q P) B) :
    actualStemCutBudget F q P ≤ B := by
  rw [actualStemCutBudget_eq_twice F q P hP hP0]
  unfold polynomialCutBudget
  rw [← finset_sup_twice]
  apply Finset.sup_le
  intro a ha
  have haq : a ≤ q := by have := Finset.mem_range.mp ha; omega
  obtain ⟨b, hq⟩ := Nat.exists_eq_add_of_le haq
  subst q
  have hs := (hB a (b + 1) (Nat.add_assoc a b 1).symm).2
  rw [actualDualSpaceCut_stem_inside, actualStemInsideCut_suffixSupport_finrank] at hs
  simpa only [Nat.add_sub_cancel_left] using hs

def prefixStateCutBudget (P : PrefixState F) : ℕ :=
  actualStemCutBudget F (2 ^ P.height - 1) P.polynomial

theorem prefixState_actualDualCutBound (P : PrefixState F) :
    ActualDualCutBound F (2 ^ P.height)
      (dualCoefficientSpace F (2 ^ P.height) (prefixSpace F P.polynomial))
        (prefixStateCutBudget F P) := by
  have hP : P.polynomial ∈ homogeneous F (2 ^ P.height - 1) :=
    (wordHomogeneous_iff_mem_homogeneous F _ _).mp P.homogeneous
  have hq : (2 ^ P.height - 1) + 1 = 2 ^ P.height := by
    have hp : 0 < (2 : ℕ) ^ P.height := pow_pos (by norm_num) _
    omega
  have hB : ActualDualCutBound F ((2 ^ P.height - 1) + 1)
      (dualCoefficientSpace F ((2 ^ P.height - 1) + 1) (prefixSpace F P.polynomial))
        (prefixStateCutBudget F P) := by
    rw [prefixSpace_dualCoefficientSpace_eq_actualStemDualSpace F _ _ P.homogeneous]
    change ActualDualCutBound F _ _ (actualStemCutBudget F _ _)
    rw [actualStemCutBudget_eq_twice F _ _ hP P.nonzero]
    exact actualStemDualSpace_cutBound F _ _ hP P.nonzero
  rw [dualCoefficientSpace_degreeCast F hq]
  exact actualDualCutBound_degreeCast F hq _ _ hB

theorem waitPrefix_cutBudget (P : PrefixState F) :
    prefixStateCutBudget F (waitPrefix F P) = prefixStateCutBudget F P := by
  unfold prefixStateCutBudget
  rw [waitPrefix_height, ← waiting_dyadic_degree]
  exact actualStemCutBudget_waiting F _ P.polynomial
    ((wordHomogeneous_iff_mem_homogeneous F _ _).mp P.homogeneous) P.nonzero

theorem waitIter_cutBudget (P : PrefixState F) (w : ℕ) :
    prefixStateCutBudget F (waitIter F P w) = prefixStateCutBudget F P := by
  induction w with
  | zero => rfl
  | succ w ih => rw [waitIter_succ, waitPrefix_cutBudget, ih]

theorem initialPrefix_cutBudget : prefixStateCutBudget F (initialPrefix F) = 2 := by
  have h1 : (1 : WordAlgebra F) ∈ homogeneous F 0 := by
    rw [homogeneous_zero_eq_span_one]
    exact Submodule.subset_span (by simp)
  change actualStemCutBudget F 0 (1 : WordAlgebra F) = 2
  rw [actualStemCutBudget_eq_twice F 0 1 h1 one_ne_zero]
  have hrho : polynomialCutBudget F 0 (1 : WordAlgebra F) = 1 := by
    simp only [polynomialCutBudget, Nat.zero_add, Finset.range_one, Finset.sup_singleton,
      Nat.sub_zero]
    exact polynomialCutRank_zero F 0 1 h1 one_ne_zero
  rw [hrho]

theorem prefixStateCutBudget_le_of_cutBound (P : PrefixState F) (B : ℕ)
    (hB : ActualDualCutBound F (2 ^ P.height)
      (dualCoefficientSpace F (2 ^ P.height) (prefixSpace F P.polynomial)) B) :
    prefixStateCutBudget F P ≤ B := by
  have hq : (2 ^ P.height - 1) + 1 = 2 ^ P.height := by
    have hp : 0 < (2 : ℕ) ^ P.height := pow_pos (by norm_num) _
    omega
  have h := actualDualCutBound_degreeCast F hq.symm _ B hB
  rw [← dualCoefficientSpace_degreeCast F hq.symm,
    prefixSpace_dualCoefficientSpace_eq_actualStemDualSpace F _ _ P.homogeneous] at h
  exact actualStemCutBudget_le_of_cutBound F _ P.polynomial
    ((wordHomogeneous_iff_mem_homogeneous F _ _).mp P.homogeneous) P.nonzero B h

/-- Actual all-cut bounds control the original completion-annihilator
dimensions at their raw strict dyadic root. -/
theorem rightCompletion_finrank_le_of_rootCutBound (W : DyadicDualData F)
    (n B : ℕ) (hn : n ≠ 0)
    (hB : ActualDualCutBound F (2 ^ strictDyadicRoot n) (W (strictDyadicRoot n)) B) :
    Module.finrank F ((homogeneousRightCompletion F W n).dualAnnihilator) ≤ B := by
  rw [homogeneousRightCompletion_dualAnnihilator_finrank_eq_tensorPrefixSupport F W n hn]
  exact (hB n (2 ^ strictDyadicRoot n - n) (completionRootDegree n)).1

theorem leftCompletion_finrank_le_of_rootCutBound (W : DyadicDualData F)
    (n B : ℕ) (hn : n ≠ 0)
    (hB : ActualDualCutBound F (2 ^ strictDyadicRoot n) (W (strictDyadicRoot n)) B) :
    Module.finrank F ((homogeneousLeftCompletion F W n).dualAnnihilator) ≤ B := by
  rw [homogeneousLeftCompletion_dualAnnihilator_finrank_eq_tensorSuffixSupport F W n hn]
  exact (hB (2 ^ strictDyadicRoot n - n) n (completionRootDegreeLeft n)).2

#print axioms CriticalGK2.Actual.prefixState_actualDualCutBound
#print axioms CriticalGK2.Actual.waitIter_cutBudget

end

end CriticalGK2.Actual
