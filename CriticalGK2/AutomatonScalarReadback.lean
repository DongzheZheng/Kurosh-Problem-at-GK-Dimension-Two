import CriticalGK2.AutomatonFiniteEvaluation
import CriticalGK2.DualWordBridge
import CriticalGK2.ScalarReadback

/-!
# Actual automaton evaluation and scalar-extension readback

The degree-`n` coefficient tensor below is formed from the actual word
coefficients of the actual generic matrix power.  Pairing it with any actual
homogeneous dual equals a coefficient of the actual matrix evaluator.
Consequently, vanishing on a specified annihilator puts this actual tensor
in the scalar extension of the specified primal subspace.

The construction's evaluator-vanishing theorem applies this readback to
the all-cut annihilator.
-/

namespace CriticalGK2.Automaton

open scoped BigOperators
open TensorProduct

noncomputable section

local instance (n : ℕ) : DecidableEq (Actual.LengthWord n) := Classical.decEq _

variable (F R : Type*) [Field F] [CommRing R] [Algebra F R]
variable {r d : ℕ}

/-- The actual homogeneous coefficient tensor of one generic matrix-power entry. -/
def genericPowerTensor (c : Coefficients R r d) (n e : ℕ) (a b : Fin r) :
    Actual.homogeneous F n ⊗[F] R :=
  ∑ w : Actual.LengthWord n,
    Actual.homogeneousWordBasis F n w ⊗ₜ[F]
      (((genericMatrix c) ^ e) a b) w.val

/-- Extended pairing is linear in its actual dual argument. -/
def dualTensorPairing {X : Type*} [AddCommGroup X] [Module F X]
    (z : X ⊗[F] R) : Module.Dual F X →ₗ[F] R where
  toFun φ := CriticalGK2.extendedPair φ z
  map_add' φ ψ := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c => simp [add_smul]
    | add z z' hz hz' => simp only [map_add, hz, hz']; abel
  map_smul' a φ := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c => simp [smul_smul]
    | add z z' hz hz' => simp only [map_add, hz, hz', smul_add]

/-- Taking a specified head coefficient of the actual homogeneous dual evaluator. -/
def evaluatedHeadCoefficient (c : Coefficients R r d) (hd : 0 < d)
    (n e : ℕ) (a b : Fin r) : Actual.HomogeneousDual F n →ₗ[F] R where
  toFun φ :=
    (Actual.actualDualMatrixEvaluation F (Polynomial R) (stateNumber r d) n
      (finiteLetterTransition c) φ (finiteHead d hd a) (finiteHead d hd b)).coeff e
  map_add' φ ψ := by
    simp only [map_add, Matrix.add_apply, Polynomial.coeff_add]
  map_smul' a φ := by
    simp only [map_smul, Matrix.smul_apply, Polynomial.coeff_smul, RingHom.id_apply]

/-- A dual word basis reconstructs its actual monomial, with coefficient one. -/
theorem dualToAmbient_dualWordBasis (n : ℕ) (w : Actual.LengthWord n) :
    Actual.dualToAmbient F n ((Actual.homogeneousWordBasis F n).dualBasis w) =
      MonoidAlgebra.single w.val (1 : F) := by
  rw [← Actual.coefficientSelfDual_basis F n w]
  change ((Actual.coefficientSelfDual F n).symm
    (Actual.coefficientSelfDual F n (Actual.homogeneousWordBasis F n w))).val = _
  rw [LinearEquiv.symm_apply_apply]
  exact Actual.homogeneousWordBasis_coe F n w

/-- The actual dual evaluator agrees with the proved actual automaton product
on every actual homogeneous word basis. -/
theorem actualDualEvaluation_dualWordBasis (c : Coefficients R r d)
    (n : ℕ) (w : Actual.LengthWord n) :
    Actual.actualDualMatrixEvaluation F (Polynomial R) (stateNumber r d) n
        (finiteLetterTransition c) ((Actual.homogeneousWordBasis F n).dualBasis w) =
      finiteWordTransition c w.val.toList := by
  simp only [Actual.actualDualMatrixEvaluation, LinearMap.comp_apply]
  rw [dualToAmbient_dualWordBasis]
  simpa only [FreeMonoid.ofList_toList, one_smul] using
    binaryEvaluation_single_finite_word F c w.val.toList (1 : F)

/-- Exact pairing identity for the original homogeneous space and actual
matrix-power coefficients.  The equality is proved on the actual dual basis. -/
theorem evaluatedHeadCoefficient_eq_extendedPair (c : Coefficients R r d)
    (hd : 0 < d) (n e : ℕ) (a b : Fin r) (φ : Actual.HomogeneousDual F n) :
    evaluatedHeadCoefficient F R c hd n e a b φ =
      CriticalGK2.extendedPair φ (genericPowerTensor F R c n e a b) := by
  classical
  have heq : evaluatedHeadCoefficient F R c hd n e a b =
      dualTensorPairing F R (genericPowerTensor F R c n e a b) := by
    apply (Actual.homogeneousWordBasis F n).dualBasis.ext
    intro w
    change (Actual.actualDualMatrixEvaluation F (Polynomial R) (stateNumber r d) n
        (finiteLetterTransition c) ((Actual.homogeneousWordBasis F n).dualBasis w)
        (finiteHead d hd a) (finiteHead d hd b)).coeff e =
      CriticalGK2.extendedPair ((Actual.homogeneousWordBasis F n).dualBasis w)
        (genericPowerTensor F R c n e a b)
    rw [actualDualEvaluation_dualWordBasis, finite_automaton_coefficient_identity]
    simp [genericPowerTensor, CriticalGK2.extendedPair_tmul,
      Module.Basis.coe_dualBasis, Module.Basis.coord_apply,
      Module.Basis.repr_self_apply, Finsupp.single_apply, FreeMonoid.ofList_toList]
  exact LinearMap.congr_fun heq φ

/-- Expanded form of the same actual pairing, for checking coefficient,
word-order and scalar-extension conventions explicitly. -/
theorem evaluatedHeadCoefficient_eq_wordPairing (c : Coefficients R r d)
    (hd : 0 < d) (n e : ℕ) (a b : Fin r) (φ : Actual.HomogeneousDual F n) :
    evaluatedHeadCoefficient F R c hd n e a b φ =
      ∑ w : Actual.LengthWord n,
        algebraMap F R (φ (Actual.homogeneousWordBasis F n w)) *
          (((genericMatrix c) ^ e) a b) w.val := by
  rw [evaluatedHeadCoefficient_eq_extendedPair]
  simp [genericPowerTensor, CriticalGK2.extendedPair_algebra_tmul, Algebra.smul_def]

/-- Vanishing of the actual evaluator on an actual annihilator implies actual
scalar-extension membership of every corresponding matrix-power component. -/
theorem genericPowerTensor_mem_scalarExtension_of_evaluation_zero
    (c : Coefficients R r d) (hd : 0 < d) (n e : ℕ) (a b : Fin r)
    (D : Submodule F (Actual.homogeneous F n))
    (hzero : ∀ φ : Actual.HomogeneousDual F n, φ ∈ D.dualAnnihilator →
      Actual.actualDualMatrixEvaluation F (Polynomial R) (stateNumber r d) n
        (finiteLetterTransition c) φ = 0) :
    genericPowerTensor F R c n e a b ∈ CriticalGK2.scalarExtension D := by
  apply CriticalGK2.mem_scalarExtension_of_extendedPair_eq_zero
  intro φ hφ
  rw [← evaluatedHeadCoefficient_eq_extendedPair F R c hd n e a b φ]
  simp [evaluatedHeadCoefficient, hzero φ hφ]

/-- The same readback in the actual vector-space quotient. -/
theorem genericPowerTensor_quotient_zero_of_evaluation_zero
    (c : Coefficients R r d) (hd : 0 < d) (n e : ℕ) (a b : Fin r)
    (D : Submodule F (Actual.homogeneous F n))
    (hzero : ∀ φ : Actual.HomogeneousDual F n, φ ∈ D.dualAnnihilator →
      Actual.actualDualMatrixEvaluation F (Polynomial R) (stateNumber r d) n
        (finiteLetterTransition c) φ = 0) :
    D.mkQ.rTensor R (genericPowerTensor F R c n e a b) = 0 := by
  have hz := genericPowerTensor_mem_scalarExtension_of_evaluation_zero F R c hd n e a b D hzero
  change genericPowerTensor F R c n e a b ∈ LinearMap.range (D.subtype.rTensor R) at hz
  rwa [← rTensor_mkQ R D, LinearMap.mem_ker] at hz

#print axioms CriticalGK2.Automaton.evaluatedHeadCoefficient_eq_extendedPair
#print axioms CriticalGK2.Automaton.genericPowerTensor_quotient_zero_of_evaluation_zero

end

end CriticalGK2.Automaton
