import CriticalGK2.VersionOne
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Scalar extension with its canonical left field action

Tensor commutation is proved multiplicative for the actual non-unital tensor
ring.  It transfers actual matrix nilness from A tensor K to K tensor A.
The latter carries Mathlib's canonical left K-module structure, with the
standard multiplication compatibility instances. Matrix nilness then gives
algebraicity of its K-unitization matrices.
-/

namespace CriticalGK2.Actual

open TensorProduct

noncomputable section

variable (F K A : Type*) [Field F] [Field K] [Algebra F K]
  [NonUnitalRing A] [Module F A] [IsScalarTower F A A] [SMulCommClass F A A]

theorem scalarTensorComm_map_mul (x y : A ⊗[F] K) :
    TensorProduct.comm F A K (x * y) =
      TensorProduct.comm F A K x * TensorProduct.comm F A K y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul, LinearEquiv.map_zero]
  | add x x' hx hx' =>
      simp only [add_mul, LinearEquiv.map_add, hx, hx']
  | tmul a c =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, LinearEquiv.map_zero]
      | add y y' hy hy' =>
          simp only [mul_add, LinearEquiv.map_add, hy, hy']
      | tmul b d =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.comm_tmul]

/-- Actual tensor commutation, equipped with its proved ring operations. -/
def scalarTensorComm : A ⊗[F] K ≃+* K ⊗[F] A where
  __ := (TensorProduct.comm F A K).toAddEquiv
  map_mul' := scalarTensorComm_map_mul F K A

@[simp]
theorem scalarTensorComm_tmul (a : A) (c : K) :
    scalarTensorComm F K A (a ⊗ₜ[F] c) = c ⊗ₜ[F] a := rfl

theorem scalarTensorComm_matrix_positivePower (r : ℕ)
    (M : Matrix (Fin r) (Fin r) (A ⊗[F] K)) (e : ℕ) :
    (CriticalGK2.positivePower M e).map (scalarTensorComm F K A) =
      CriticalGK2.positivePower (M.map (scalarTensorComm F K A)) e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [CriticalGK2.positivePower, Matrix.map_mul, ih]
      rfl

/-- Matrix nilness transports to the same scalar-extended algebra in the
canonical left K-module presentation. -/
theorem left_scalar_matrix_nil_of_right_scalar_matrix_nil
    (matrixNil : ∀ r : ℕ, 0 < r → ∀ M : Matrix (Fin r) (Fin r) (A ⊗[F] K),
      ∃ e : ℕ, CriticalGK2.positivePower M e = 0) :
    ∀ r : ℕ, 0 < r → ∀ M : Matrix (Fin r) (Fin r) (K ⊗[F] A),
      ∃ e : ℕ, CriticalGK2.positivePower M e = 0 := by
  intro r hr M
  let U : Matrix (Fin r) (Fin r) (A ⊗[F] K) :=
    M.map (scalarTensorComm F K A).symm
  obtain ⟨e, he⟩ := matrixNil r hr U
  have hU : U.map (scalarTensorComm F K A) = M := by
    apply Matrix.ext
    intro i j
    exact (scalarTensorComm F K A).apply_symm_apply (M i j)
  have htransport := scalarTensorComm_matrix_positivePower F K A r U e
  rw [hU, he] at htransport
  refine ⟨e, htransport.symm.trans ?_⟩
  apply Matrix.ext
  intro i j
  exact map_zero (scalarTensorComm F K A)

/-- Actual K-unitization algebraicity, applied to the proved nil input for
the original actual scalar-extended algebra. -/
theorem scalarExtension_unitization_matrix_algebraic
    (matrixNil : ∀ r : ℕ, 0 < r → ∀ M : Matrix (Fin r) (Fin r) (A ⊗[F] K),
      ∃ e : ℕ, CriticalGK2.positivePower M e = 0) :
    ∀ r : ℕ, 0 < r →
      Algebra.IsAlgebraic K
        (Matrix (Fin r) (Fin r) (Unitization K (K ⊗[F] A))) := by
  exact CriticalGK2.VersionOne.capstone
    (left_scalar_matrix_nil_of_right_scalar_matrix_nil F K A matrixNil)

#print axioms CriticalGK2.Actual.scalarTensorComm
#print axioms CriticalGK2.Actual.scalarExtension_unitization_matrix_algebraic

end

end CriticalGK2.Actual
