import CriticalGK2.ScalarExtensionUnitization
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Actual scalar base change of the actual unitization

An explicit composition of genuine tensor, product and unitization linear
equivalences is proved multiplicative by two tensor inductions. The source
uses the actual right K-algebra structure. Its pure tensor formula also
proves compatibility with K's algebra map. Matrix algebraicity therefore
passes to the literal tensor product of the original F-unitization.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F K A : Type*) [Field F] [Field K] [Algebra F K]
  [NonUnitalRing A] [Module F A] [IsScalarTower F A A] [SMulCommClass F A A]

/-- The additive and F-linear decomposition of the scalar-extended
unitization. -/
def unitizationScalarLinearEquiv :
    (Unitization F A) ⊗[F] K ≃ₗ[F] Unitization K (K ⊗[F] A) :=
  (TensorProduct.comm F (Unitization F A) K).trans
    ((TensorProduct.congr (LinearEquiv.refl F K) (Unitization.linearEquiv F F A)).trans
      ((TensorProduct.prodRight F F K F A).trans
        (((TensorProduct.rid F K).prodCongr (LinearEquiv.refl F (K ⊗[F] A))).trans
          (Unitization.linearEquiv F K (K ⊗[F] A)).symm)))

@[simp]
theorem unitizationScalarLinearEquiv_tmul (u : Unitization F A) (c : K) :
    unitizationScalarLinearEquiv F K A (u ⊗ₜ[F] c) =
      Unitization.mk (u.fst • c, c ⊗ₜ[F] u.snd) := by
  simp only [unitizationScalarLinearEquiv, LinearEquiv.trans_apply,
    TensorProduct.comm_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    Unitization.linearEquiv_apply, TensorProduct.prodRight_tmul,
    LinearEquiv.prodCongr_apply, TensorProduct.rid_tmul,
    Unitization.linearEquiv_symm_apply]

/-- The actual compatibility between the old F-action and the new left
K-action on pure tensors. -/
theorem unitizationBaseChange_scalar_tensor (a : F) (c d : K) (z : A) :
    (c * d) ⊗ₜ[F] (a • z) = (a • c) • (d ⊗ₜ[F] z) := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  change (a • (c * d)) ⊗ₜ[F] z = ((a • c) * d) ⊗ₜ[F] z
  rw [smul_mul_assoc]

/-- Actual pure tensor multiplication, including both mixed scalar terms
in the unitization multiplication formula. -/
theorem unitizationScalarLinearEquiv_tmul_mul
    (u v : Unitization F A) (c d : K) :
    unitizationScalarLinearEquiv F K A ((u ⊗ₜ[F] c) * (v ⊗ₜ[F] d)) =
      unitizationScalarLinearEquiv F K A (u ⊗ₜ[F] c) *
        unitizationScalarLinearEquiv F K A (v ⊗ₜ[F] d) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    unitizationScalarLinearEquiv_tmul,
    unitizationScalarLinearEquiv_tmul, unitizationScalarLinearEquiv_tmul]
  apply Unitization.ext
  · change (u.fst * v.fst) • (c * d) = (u.fst • c) * (v.fst • d)
    simp only [Algebra.smul_def, map_mul]
    ring
  · change (c * d) ⊗ₜ[F] (u * v).snd =
      (u.fst • c) • (d ⊗ₜ[F] v.snd) + (v.fst • d) • (c ⊗ₜ[F] u.snd) +
        (c ⊗ₜ[F] u.snd) * (d ⊗ₜ[F] v.snd)
    have hleft := unitizationBaseChange_scalar_tensor F K A u.fst c d v.snd
    have hright := unitizationBaseChange_scalar_tensor F K A v.fst d c u.snd
    rw [mul_comm d c] at hright
    rw [Unitization.snd_mul, TensorProduct.tmul_add, TensorProduct.tmul_add,
      hleft, hright, Algebra.TensorProduct.tmul_mul_tmul]

/-- Actual multiplicativity for all tensors, proved by tensor induction. -/
theorem unitizationScalarLinearEquiv_map_mul
    (x y : (Unitization F A) ⊗[F] K) :
    unitizationScalarLinearEquiv F K A (x * y) =
      unitizationScalarLinearEquiv F K A x * unitizationScalarLinearEquiv F K A y := by
  let μ : (Unitization F A) ⊗[F] K →ₗ[F]
      (Unitization F A) ⊗[F] K →ₗ[F] (Unitization F A) ⊗[F] K :=
    Algebra.TensorProduct.mul
  induction x using TensorProduct.induction_on with
  | zero =>
      have hm : (0 : (Unitization F A) ⊗[F] K) * y = 0 := by
        change (μ 0) y = 0
        rw [μ.map_zero, LinearMap.zero_apply]
      rw [hm, (unitizationScalarLinearEquiv F K A).map_zero, zero_mul]
  | add x x' hx hx' =>
      have hm : (x + x') * y = x * y + x' * y := by
        change μ (x + x') y = μ x y + μ x' y
        rw [μ.map_add, LinearMap.add_apply]
      rw [hm, (unitizationScalarLinearEquiv F K A).map_add, hx, hx',
        (unitizationScalarLinearEquiv F K A).map_add, add_mul]
  | tmul u c =>
      induction y using TensorProduct.induction_on with
      | zero =>
          have hm : (u ⊗ₜ[F] c) * (0 : (Unitization F A) ⊗[F] K) = 0 := by
            change μ (u ⊗ₜ[F] c) 0 = 0
            exact (μ (u ⊗ₜ[F] c)).map_zero
          rw [hm, (unitizationScalarLinearEquiv F K A).map_zero, mul_zero]
      | add y y' hy hy' =>
          have hm : (u ⊗ₜ[F] c) * (y + y') =
              (u ⊗ₜ[F] c) * y + (u ⊗ₜ[F] c) * y' := by
            change μ (u ⊗ₜ[F] c) (y + y') =
              μ (u ⊗ₜ[F] c) y + μ (u ⊗ₜ[F] c) y'
            exact (μ (u ⊗ₜ[F] c)).map_add y y'
          rw [hm, (unitizationScalarLinearEquiv F K A).map_add, hy, hy',
            (unitizationScalarLinearEquiv F K A).map_add, mul_add]
      | tmul v d => exact unitizationScalarLinearEquiv_tmul_mul F K A u v c d

/-- The preceding actual linear equivalence with its proved multiplication. -/
def unitizationScalarRingEquiv :
    (Unitization F A) ⊗[F] K ≃+* Unitization K (K ⊗[F] A) where
  __ := (unitizationScalarLinearEquiv F K A).toAddEquiv
  map_mul' := unitizationScalarLinearEquiv_map_mul F K A

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual K-algebra equivalence, using the literal right K-algebra
structure on the source tensor product. -/
def unitizationRightScalarAlgEquiv :
    (Unitization F A) ⊗[F] K ≃ₐ[K] Unitization K (K ⊗[F] A) where
  __ := unitizationScalarRingEquiv F K A
  commutes' c := by
    change unitizationScalarLinearEquiv F K A ((1 : Unitization F A) ⊗ₜ[F] c) =
      Unitization.inl c
    rw [unitizationScalarLinearEquiv_tmul]
    apply Unitization.ext
    · simp only [Unitization.fst_one, one_smul, Unitization.fst_inl]
    · simp only [Unitization.snd_one, TensorProduct.tmul_zero, Unitization.snd_inl]

/-- Every matrix over the literal scalar extension of the original
F-unitization is algebraic, supplied by actual absolute matrix nilness of A.
The scalar extension/unitization identification is proved above. -/
theorem unitization_tensor_matrix_algebraic_of_scalar_matrix_nil
    (hsource : ∀ r : ℕ, 0 < r →
      ∀ M : Matrix (Fin r) (Fin r) (A ⊗[F] K), ∃ e : ℕ, positivePower M e = 0) :
    ∀ r : ℕ, 0 < r → Algebra.IsAlgebraic K
      (Matrix (Fin r) (Fin r) ((Unitization F A) ⊗[F] K)) := by
  intro r hr
  letI : Algebra.IsAlgebraic K
      (Matrix (Fin r) (Fin r) (Unitization K (K ⊗[F] A))) :=
    scalarExtension_unitization_matrix_algebraic F K A hsource r hr
  let π : Matrix (Fin r) (Fin r) ((Unitization F A) ⊗[F] K) →ₐ[K]
      Matrix (Fin r) (Fin r) (Unitization K (K ⊗[F] A)) :=
    (unitizationRightScalarAlgEquiv F K A).toAlgHom.mapMatrix
  have hπ : Function.Injective π := by
    intro M N h
    apply Matrix.ext
    intro i j
    apply (unitizationRightScalarAlgEquiv F K A).injective
    exact congrFun (congrFun h i) j
  exact Algebra.IsAlgebraic.of_injective π hπ

#print axioms CriticalGK2.Actual.unitizationRightScalarAlgEquiv
#print axioms CriticalGK2.Actual.unitization_tensor_matrix_algebraic_of_scalar_matrix_nil

end

end CriticalGK2.Actual
