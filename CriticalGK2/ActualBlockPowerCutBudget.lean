import CriticalGK2.ActualProductCutBudget
import CriticalGK2.ActualCutDimension

/-!
# Actual multiplication powers and their literal cut budgets

The intermediate spaces are the actual multiplication powers of the incoming
two-dimensional prefix space. Their dimensions are bounded by 2^m.
Every complete cut support is bounded by 2^m times the incoming support budget.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct CriticalGK2.ContractionBudget

variable (F : Type*) [Field F]

/-- On an actual homogeneous subspace, coefficient self-duality loses no
dimension. The inverse is the proved actual coefficient reconstruction. -/
theorem dualCoefficientSpace_finrank_eq (q : ℕ)
    (S : Submodule F (WordAlgebra F)) (hS : S ≤ homogeneous F q) :
    Module.finrank F (dualCoefficientSpace F q S) = Module.finrank F S := by
  let f : S →ₗ[F] HomogeneousDual F q := (ambientToDual F q).comp S.subtype
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg (dualToAmbient F q) hxy
    change dualToAmbient F q (ambientToDual F q x.val) =
      dualToAmbient F q (ambientToDual F q y.val) at h
    rw [dualToAmbient_ambientToDual F q x.val (hS x.property),
      dualToAmbient_ambientToDual F q y.val (hS y.property)] at h
    exact h
  have hr : LinearMap.range f = dualCoefficientSpace F q S := by
    change LinearMap.range ((ambientToDual F q).comp S.subtype) = _
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  rw [← hr]
  exact LinearMap.finrank_range_of_inj hf

theorem homogeneousDual_zero_finrank_for_budget :
    Module.finrank F (HomogeneousDual F 0) = 1 := by
  rw [← (coefficientSelfDual F 0).finrank_eq, finrank_homogeneous_zero]

/-- The actual degree-zero cut has scalar factors on both sides. -/
theorem actualDualCutBound_zero (W : Submodule F (HomogeneousDual F 0))
    (B : ℕ) (hB : 1 ≤ B) : ActualDualCutBound F 0 W B := by
  classical
  intro a b hab
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  subst a
  subst b
  letI : FiniteDimensional F (HomogeneousDual F 0) :=
    (homogeneousWordBasis F 0).dualBasis.finiteDimensional_of_finite
  constructor
  · calc
      _ ≤ Module.finrank F (HomogeneousDual F 0) := by
        simpa only [finrank_top] using Submodule.finrank_mono
          (show tensorPrefixSupport (actualDualSpaceCut F 0 0 0 hab W) ≤ ⊤ from le_top)
      _ = 1 := homogeneousDual_zero_finrank_for_budget F
      _ ≤ B := hB
  · calc
      _ ≤ Module.finrank F (HomogeneousDual F 0) := by
        simpa only [finrank_top] using Submodule.finrank_mono
          (show tensorSuffixSupport (actualDualSpaceCut F 0 0 0 hab W) ≤ ⊤ from le_top)
      _ = 1 := homogeneousDual_zero_finrank_for_budget F
      _ ≤ B := hB

/-- Every actual intermediate m-block coefficient space has dimension at
most 2^m. This includes the actual scalar zero-block space. -/
theorem blockPower_dualCoefficientSpace_finrank_le (q : ℕ)
    (S : Submodule F (WordAlgebra F)) (hS : S ≤ homogeneous F q)
    (hSdim : Module.finrank F (dualCoefficientSpace F q S) ≤ 2) (m : ℕ) :
    Module.finrank F (dualCoefficientSpace F (m * q) (blockPower F S m)) ≤ 2 ^ m := by
  classical
  induction m with
  | zero =>
      rw [dualCoefficientSpace_degreeCast F (Nat.zero_mul q).symm,
        (homogeneousDualDegreeCast F (Nat.zero_mul q).symm).finrank_map_eq,
        blockPower_zero, dualCoefficientSpace_finrank_eq F 0 (homogeneous F 0) le_rfl,
        pow_zero]
      exact le_of_eq (finrank_homogeneous_zero F)
  | succ m ih =>
      letI : FiniteDimensional F (HomogeneousDual F (m * q + q)) :=
        (homogeneousWordBasis F (m * q + q)).dualBasis.finiteDimensional_of_finite
      rw [Nat.succ_mul, blockPower_succ]
      calc
        _ ≤ Module.finrank F (actualDualTensorProduct F (m * q) q
            (dualCoefficientSpace F (m * q) (blockPower F S m))
            (dualCoefficientSpace F q S)) :=
          Submodule.finrank_mono (dualCoefficientSpace_productSpan_le F (m * q) q _ _
            (blockPower_le_homogeneous F S q hS m) hS)
        _ ≤ Module.finrank F (dualCoefficientSpace F (m * q) (blockPower F S m)) *
            Module.finrank F (dualCoefficientSpace F q S) :=
          actualDualTensorProduct_finrank_le F (m * q) q _ _
        _ ≤ 2 ^ m * 2 := Nat.mul_le_mul ih hSdim
        _ = 2 ^ (m + 1) := (pow_succ 2 m).symm

/-- All literal cut supports of the actual m-block space are paid by the
actual intermediate dimensions. The incoming cut bound is the only support
hypothesis, and is applied to an actual homogeneous subspace. -/
theorem blockPower_actualDualCutBound (q : ℕ)
    (S : Submodule F (WordAlgebra F)) (hS : S ≤ homogeneous F q)
    (hSdim : Module.finrank F (dualCoefficientSpace F q S) ≤ 2)
    (B : ℕ) (hBpos : 1 ≤ B)
    (hB : ActualDualCutBound F q (dualCoefficientSpace F q S) B) (m : ℕ) :
    ActualDualCutBound F (m * q)
      (dualCoefficientSpace F (m * q) (blockPower F S m)) (2 ^ m * B) := by
  induction m with
  | zero =>
      have h := actualDualCutBound_degreeCast F (Nat.zero_mul q).symm _ B
        (actualDualCutBound_zero F
          (dualCoefficientSpace F 0 (blockPower F S 0)) B hBpos)
      rw [← dualCoefficientSpace_degreeCast F (Nat.zero_mul q).symm] at h
      simpa only [pow_zero, one_mul] using h
  | succ m ih =>
      rw [Nat.succ_mul, blockPower_succ]
      apply actualDualCutBound_mono F (m * q + q)
        (dualCoefficientSpace_productSpan_le F (m * q) q _ _
          (blockPower_le_homogeneous F S q hS m) hS) (2 ^ (m + 1) * B)
      have hpow : 2 ^ m ≤ (2 : ℕ) ^ (m + 1) := by
        rw [pow_succ]
        omega
      have hpowpos : 1 ≤ (2 : ℕ) ^ (m + 1) :=
        Nat.succ_le_of_lt (pow_pos (by norm_num) _)
      apply actualDualTensorProduct_cutBound F (m * q) q _ _ (2 ^ m * B) B
        (2 ^ (m + 1) * B) ih hB
      · exact Nat.mul_le_mul_right B hpow
      · calc
          _ ≤ (2 ^ m * B) * 2 := Nat.mul_le_mul_left _ hSdim
          _ = 2 ^ (m + 1) * B := by rw [pow_succ]; ac_rfl
      · simpa only [one_mul] using Nat.mul_le_mul_right B hpowpos
      · exact (Nat.mul_le_mul_right B
          (blockPower_dualCoefficientSpace_finrank_le F q S hS hSdim m)).trans
          (Nat.mul_le_mul_right B hpow)

theorem prefixStateSpace_le_homogeneous (P : PrefixState F) :
    prefixSpace F P.polynomial ≤ homogeneous F (2 ^ P.height) := by
  simpa only [piSegment_zero, Nat.add_zero] using piSegment_le_homogeneous F P 0 0

theorem prefixStateSpace_dualCoefficient_finrank (P : PrefixState F) :
    Module.finrank F
      (dualCoefficientSpace F (2 ^ P.height) (prefixSpace F P.polynomial)) = 2 := by
  have hq : (2 ^ P.height - 1) + 1 = 2 ^ P.height := by
    have hp : 0 < (2 : ℕ) ^ P.height := pow_pos (by norm_num) _
    omega
  rw [dualCoefficientSpace_degreeCast F hq,
    (homogeneousDualDegreeCast F hq).finrank_map_eq,
    prefixSpace_dualCoefficientSpace_eq_actualStemDualSpace F _ _ P.homogeneous]
  exact actualStemDualSpace_finrank F _ P.polynomial
    ((wordHomogeneous_iff_mem_homogeneous F _ _).mp P.homogeneous) P.nonzero

theorem prefixStateCutBudget_pos (P : PrefixState F) : 1 ≤ prefixStateCutBudget F P := by
  have hp := polynomialCutBudget_pos F _ P.polynomial
    ((wordHomogeneous_iff_mem_homogeneous F _ _).mp P.homogeneous) P.nonzero
  unfold prefixStateCutBudget
  rw [actualStemCutBudget_eq_twice F _ P.polynomial
    ((wordHomogeneous_iff_mem_homogeneous F _ _).mp P.homogeneous) P.nonzero]
  omega

/-- The prefix state satisfies the hypotheses of the block-power bound. -/
theorem prefixState_blockPower_cutBound (P : PrefixState F) (m : ℕ) :
    ActualDualCutBound F (m * 2 ^ P.height)
      (dualCoefficientSpace F (m * 2 ^ P.height)
        (blockPower F (prefixSpace F P.polynomial) m))
      (2 ^ m * prefixStateCutBudget F P) :=
  blockPower_actualDualCutBound F _ _ (prefixStateSpace_le_homogeneous F P)
    (le_of_eq (prefixStateSpace_dualCoefficient_finrank F P)) _
    (prefixStateCutBudget_pos F P) (prefixState_actualDualCutBound F P) m

#print axioms CriticalGK2.Actual.blockPower_actualDualCutBound
#print axioms CriticalGK2.Actual.prefixState_blockPower_cutBound

end

end CriticalGK2.Actual
