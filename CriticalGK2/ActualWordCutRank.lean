import CriticalGK2.TensorCutRankTransport
import CriticalGK2.RootContractionTensorBridge
import CriticalGK2.PolynomialStages

/-!
# Actual homogeneous word cut ranks

Every cut is obtained from the inverse of the already proved actual dual
concatenation equivalence. Its prefix and suffix supports are the ranges of
the honest whole-functional flattenings. The fixed-factor laws below are
proved for actual word multiplication, with every degree cast displayed.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct CriticalGK2.ContractionBudget

variable (F : Type*) [Field F]

/-- The actual two-factor tensor at the literal cut `(a,b)`. -/
def wordCutTensor (a b : ℕ) (phi : HomogeneousDual F (a + b)) :
    HomogeneousDual F a ⊗[F] HomogeneousDual F b :=
  (homogeneousDualTensorConcat F a b).symm phi

def wordPrefixCutSupport (a b : ℕ) (phi : HomogeneousDual F (a + b)) :
    Submodule F (HomogeneousDual F a) :=
  LinearMap.range (leftFlattening (wordCutTensor F a b phi))

def wordSuffixCutSupport (a b : ℕ) (phi : HomogeneousDual F (a + b)) :
    Submodule F (HomogeneousDual F b) :=
  LinearMap.range (rightFlattening (wordCutTensor F a b phi))

def wordCutRank (a b : ℕ) (phi : HomogeneousDual F (a + b)) : ℕ :=
  tensorCutRank (wordCutTensor F a b phi)

/-- The actual prefix and suffix supports at each cut have equal dimension. -/
theorem wordSuffixCutSupport_finrank (a b : ℕ) (phi : HomogeneousDual F (a + b)) :
    Module.finrank F (wordSuffixCutSupport F a b phi) = wordCutRank F a b phi := by
  classical
  letI : FiniteDimensional F (HomogeneousDual F a) :=
    (homogeneousWordBasis F a).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (HomogeneousDual F b) :=
    (homogeneousWordBasis F b).dualBasis.finiteDimensional_of_finite
  exact rightFlattening_finrank_eq_left (wordCutTensor F a b phi)

/-- Actual dual word multiplication associativity for an arbitrary two-factor
tensor, not merely a pure tensor. -/
theorem homogeneousDualTensorConcat_associative_rightTensor (a b c : ℕ)
    (u : HomogeneousDual F a ⊗[F] HomogeneousDual F b) (theta : HomogeneousDual F c) :
    homogeneousDualDegreeCast F (Nat.add_assoc a b c)
      (homogeneousDualTensorConcat F (a + b) c
        (homogeneousDualTensorConcat F a b u ⊗ₜ[F] theta)) =
      homogeneousDualTensorConcat F a (b + c)
        ((homogeneousDualTensorConcat F b c).lTensor (HomogeneousDual F a)
          (TensorProduct.assoc F (HomogeneousDual F a) (HomogeneousDual F b)
            (HomogeneousDual F c) (u ⊗ₜ[F] theta))) := by
  induction u using TensorProduct.induction_on with
  | zero =>
      simp only [(homogeneousDualTensorConcat F a b).map_zero, zero_tmul,
        (homogeneousDualTensorConcat F (a + b) c).map_zero,
        (homogeneousDualDegreeCast F (Nat.add_assoc a b c)).map_zero,
        (TensorProduct.assoc F (HomogeneousDual F a) (HomogeneousDual F b)
          (HomogeneousDual F c)).map_zero,
        ((homogeneousDualTensorConcat F b c).lTensor (HomogeneousDual F a)).map_zero,
        (homogeneousDualTensorConcat F a (b + c)).map_zero]
  | add x y hx hy =>
      simp only [(homogeneousDualTensorConcat F a b).map_add, add_tmul,
        (homogeneousDualTensorConcat F (a + b) c).map_add,
        (homogeneousDualDegreeCast F (Nat.add_assoc a b c)).map_add,
        (TensorProduct.assoc F (HomogeneousDual F a) (HomogeneousDual F b)
          (HomogeneousDual F c)).map_add,
        ((homogeneousDualTensorConcat F b c).lTensor (HomogeneousDual F a)).map_add,
        (homogeneousDualTensorConcat F a (b + c)).map_add, hx, hy]
  | tmul phi psi =>
      simpa only [TensorProduct.assoc_tmul, LinearEquiv.lTensor_tmul] using
        homogeneousDualTensorConcat_associative F a b c phi psi theta

/-- Actual associativity with the arbitrary tensor in the last two factors. -/
theorem homogeneousDualTensorConcat_associative_leftTensor (a b c : ℕ)
    (theta : HomogeneousDual F a) (u : HomogeneousDual F b ⊗[F] HomogeneousDual F c) :
    homogeneousDualDegreeCast F (Nat.add_assoc a b c)
      (homogeneousDualTensorConcat F (a + b) c
        ((homogeneousDualTensorConcat F a b).rTensor (HomogeneousDual F c)
          ((TensorProduct.assoc F (HomogeneousDual F a) (HomogeneousDual F b)
            (HomogeneousDual F c)).symm (theta ⊗ₜ[F] u)))) =
      homogeneousDualTensorConcat F a (b + c)
        (theta ⊗ₜ[F] homogeneousDualTensorConcat F b c u) := by
  induction u using TensorProduct.induction_on with
  | zero =>
      simp only [tmul_zero,
        (TensorProduct.assoc F (HomogeneousDual F a) (HomogeneousDual F b)
          (HomogeneousDual F c)).symm.map_zero,
        ((homogeneousDualTensorConcat F a b).rTensor (HomogeneousDual F c)).map_zero,
        (homogeneousDualTensorConcat F (a + b) c).map_zero,
        (homogeneousDualDegreeCast F (Nat.add_assoc a b c)).map_zero,
        (homogeneousDualTensorConcat F b c).map_zero,
        (homogeneousDualTensorConcat F a (b + c)).map_zero]
  | add x y hx hy =>
      simp only [tmul_add,
        (TensorProduct.assoc F (HomogeneousDual F a) (HomogeneousDual F b)
          (HomogeneousDual F c)).symm.map_add,
        ((homogeneousDualTensorConcat F a b).rTensor (HomogeneousDual F c)).map_add,
        (homogeneousDualTensorConcat F (a + b) c).map_add,
        (homogeneousDualDegreeCast F (Nat.add_assoc a b c)).map_add,
        (homogeneousDualTensorConcat F b c).map_add,
        (homogeneousDualTensorConcat F a (b + c)).map_add, hx, hy]
  | tmul phi psi =>
      simpa only [TensorProduct.assoc_symm_tmul, LinearEquiv.rTensor_tmul] using
        homogeneousDualTensorConcat_associative F a b c theta phi psi

/-- The actual cut tensor after adding a last homogeneous block. -/
theorem wordCutTensor_append (a b c : ℕ) (phi : HomogeneousDual F (a + b))
    (theta : HomogeneousDual F c) :
    wordCutTensor F a (b + c)
      (homogeneousDualDegreeCast F (Nat.add_assoc a b c)
        (homogeneousDualTensorConcat F (a + b) c (phi ⊗ₜ[F] theta))) =
      (homogeneousDualTensorConcat F b c).lTensor (HomogeneousDual F a)
        (TensorProduct.assoc F (HomogeneousDual F a) (HomogeneousDual F b)
          (HomogeneousDual F c) (wordCutTensor F a b phi ⊗ₜ[F] theta)) := by
  apply (homogeneousDualTensorConcat F a (b + c)).injective
  change homogeneousDualTensorConcat F a (b + c)
    ((homogeneousDualTensorConcat F a (b + c)).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  have h := homogeneousDualTensorConcat_associative_rightTensor F a b c
    (wordCutTensor F a b phi) theta
  simpa only [wordCutTensor, LinearEquiv.apply_symm_apply] using h

/-- The actual cut tensor after adding a first homogeneous block. -/
theorem wordCutTensor_prepend (c a b : ℕ) (theta : HomogeneousDual F c)
    (phi : HomogeneousDual F (a + b)) :
    wordCutTensor F (c + a) b
      ((homogeneousDualDegreeCast F (Nat.add_assoc c a b)).symm
        (homogeneousDualTensorConcat F c (a + b) (theta ⊗ₜ[F] phi))) =
      (homogeneousDualTensorConcat F c a).rTensor (HomogeneousDual F b)
        ((TensorProduct.assoc F (HomogeneousDual F c) (HomogeneousDual F a)
          (HomogeneousDual F b)).symm (theta ⊗ₜ[F] wordCutTensor F a b phi)) := by
  apply (homogeneousDualTensorConcat F (c + a) b).injective
  apply (homogeneousDualDegreeCast F (Nat.add_assoc c a b)).injective
  change homogeneousDualDegreeCast F (Nat.add_assoc c a b)
    (homogeneousDualTensorConcat F (c + a) b
      ((homogeneousDualTensorConcat F (c + a) b).symm _)) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have h := homogeneousDualTensorConcat_associative_leftTensor F c a b theta
    (wordCutTensor F a b phi)
  simpa only [wordCutTensor, LinearEquiv.apply_symm_apply] using h.symm

/-- Appending an arbitrary actual nonzero homogeneous block preserves every
cut lying inside the old block. -/
theorem wordCutRank_append (a b c : ℕ) (phi : HomogeneousDual F (a + b))
    (theta : HomogeneousDual F c) (htheta : theta ≠ 0) :
    wordCutRank F a (b + c)
      (homogeneousDualDegreeCast F (Nat.add_assoc a b c)
        (homogeneousDualTensorConcat F (a + b) c (phi ⊗ₜ[F] theta))) =
      wordCutRank F a b phi := by
  unfold wordCutRank
  rw [wordCutTensor_append]
  exact tensorCutRank_append_transport (F := F) (X := HomogeneousDual F a)
    (Y := HomogeneousDual F b) (Z := HomogeneousDual F c)
    (A := HomogeneousDual F (b + c)) (homogeneousDualTensorConcat F b c)
      (wordCutTensor F a b phi) theta htheta

/-- Prepending an arbitrary actual nonzero block likewise preserves every
cut lying inside the old block. -/
theorem wordCutRank_prepend (c a b : ℕ) (theta : HomogeneousDual F c)
    (htheta : theta ≠ 0) (phi : HomogeneousDual F (a + b)) :
    wordCutRank F (c + a) b
      ((homogeneousDualDegreeCast F (Nat.add_assoc c a b)).symm
        (homogeneousDualTensorConcat F c (a + b) (theta ⊗ₜ[F] phi))) =
      wordCutRank F a b phi := by
  unfold wordCutRank
  rw [wordCutTensor_prepend]
  exact tensorCutRank_prepend_transport (F := F) (X := HomogeneousDual F a)
    (Y := HomogeneousDual F b) (Z := HomogeneousDual F c)
    (A := HomogeneousDual F (c + a)) (homogeneousDualTensorConcat F c a)
      theta htheta (wordCutTensor F a b phi)

/-- Literal actual homogeneous products are nonzero when both physical
blocks are nonzero. This uses the proved nonzero fixed-tensor injection. -/
theorem homogeneousDualTensorConcat_ne_zero (a b : ℕ)
    (phi : HomogeneousDual F a) (hphi : phi ≠ 0)
    (psi : HomogeneousDual F b) (hpsi : psi ≠ 0) :
    homogeneousDualTensorConcat F a b (phi ⊗ₜ[F] psi) ≠ 0 := by
  intro h
  have hz : phi ⊗ₜ[F] psi = 0 := by
    apply (homogeneousDualTensorConcat F a b).injective
    rw [h, (homogeneousDualTensorConcat F a b).map_zero]
  apply hphi
  apply fixed_right_tensor_injective (F := F) (X := HomogeneousDual F a)
    (Y := HomogeneousDual F b) psi hpsi
  simpa only [zero_tmul] using hz

#print axioms CriticalGK2.Actual.wordCutRank_append
#print axioms CriticalGK2.Actual.wordCutRank_prepend

end

end CriticalGK2.Actual
