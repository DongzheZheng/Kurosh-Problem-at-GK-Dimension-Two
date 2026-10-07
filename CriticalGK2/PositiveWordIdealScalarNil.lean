import CriticalGK2.PositiveWordIdealTransfer
import CriticalGK2.SparseAbsoluteMatrixNil
import CriticalGK2.ScalarExtensionUnitization

/-!
# Actual scalar-extension nilness of the new positive quotient

The actual positive quotient map is extended by the actual linear rTensor.
Its multiplicativity is proved by tensor induction, and its surjectivity by
right exactness of the actual tensor map. Actual finite matrices are lifted
entry by entry and their positive powers descend. The final sparse endpoints
follow from the nil theorem for the original algebra.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
variable {A B : Type*}
  [NonUnitalRing A] [Module F A] [IsScalarTower F A A] [SMulCommClass F A A]
  [NonUnitalRing B] [Module F B] [IsScalarTower F B B] [SMulCommClass F B B]

/-- The actual linear map underlying a literal non-unital algebra map. -/
def nonUnitalMapLinear (f : A →ₙₐ[F] B) : A →ₗ[F] B where
  toFun := f
  map_add' := f.map_add
  map_smul' := f.map_smul

/-- The actual right scalar extension of the literal underlying linear map. -/
def scalarTensorNonUnitalMapLinear (f : A →ₙₐ[F] B) :
    A ⊗[F] K →ₗ[F] B ⊗[F] K := (nonUnitalMapLinear F f).rTensor K

theorem scalarTensorNonUnitalMapLinear_map_mul (f : A →ₙₐ[F] B)
    (x y : A ⊗[F] K) :
    scalarTensorNonUnitalMapLinear F K f (x * y) =
      scalarTensorNonUnitalMapLinear F K f x * scalarTensorNonUnitalMapLinear F K f y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul, LinearMap.map_zero]
  | add x x' hx hx' => simp only [add_mul, LinearMap.map_add, hx, hx']
  | tmul a c =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, LinearMap.map_zero]
      | add y y' hy hy' => simp only [mul_add, LinearMap.map_add, hy, hy']
      | tmul b d =>
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          simp only [scalarTensorNonUnitalMapLinear, LinearMap.rTensor_tmul]
          change f (a * b) ⊗ₜ[F] (c * d) =
            (f a ⊗ₜ[F] c) * (f b ⊗ₜ[F] d)
          rw [f.map_mul]
          exact (Algebra.TensorProduct.tmul_mul_tmul (f a) (f b) c d).symm

/-- Tensor multiplicativity is supplied by the preceding actual proof. -/
def scalarTensorNonUnitalMap (f : A →ₙₐ[F] B) :
    A ⊗[F] K →ₙₐ[F] B ⊗[F] K where
  toFun := scalarTensorNonUnitalMapLinear F K f
  map_zero' := (scalarTensorNonUnitalMapLinear F K f).map_zero
  map_add' := (scalarTensorNonUnitalMapLinear F K f).map_add
  map_mul' := scalarTensorNonUnitalMapLinear_map_mul F K f
  map_smul' c x := (scalarTensorNonUnitalMapLinear F K f).map_smul c x

@[simp]
theorem scalarTensorNonUnitalMap_tmul (f : A →ₙₐ[F] B) (a : A) (c : K) :
    scalarTensorNonUnitalMap F K f (a ⊗ₜ[F] c) = f a ⊗ₜ[F] c := by
  change ((nonUnitalMapLinear F f).rTensor K) (a ⊗ₜ[F] c) = f a ⊗ₜ[F] c
  rw [LinearMap.rTensor_tmul]
  rfl

theorem scalarTensorNonUnitalMap_surjective (f : A →ₙₐ[F] B)
    (hf : Function.Surjective f) : Function.Surjective (scalarTensorNonUnitalMap F K f) := by
  change Function.Surjective ((nonUnitalMapLinear F f).rTensor K)
  exact LinearMap.rTensor_surjective K
    (show Function.Surjective (nonUnitalMapLinear F f) from hf)

theorem scalarTensorNonUnitalMap_matrix_positivePower (f : A →ₙₐ[F] B)
    (r : ℕ) (M : Matrix (Fin r) (Fin r) (A ⊗[F] K)) (e : ℕ) :
    (positivePower M e).map (scalarTensorNonUnitalMap F K f) =
      positivePower (M.map (scalarTensorNonUnitalMap F K f)) e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [positivePower, Matrix.map_mul, ih]
      rfl

/-- Actual entrywise lifts of every target matrix after scalar extension. -/
theorem scalarTensorNonUnitalMap_matrix_lift (f : A →ₙₐ[F] B)
    (hf : Function.Surjective f) (r : ℕ)
    (M : Matrix (Fin r) (Fin r) (B ⊗[F] K)) :
    ∃ L : Matrix (Fin r) (Fin r) (A ⊗[F] K),
      L.map (scalarTensorNonUnitalMap F K f) = M := by
  classical
  have hs := scalarTensorNonUnitalMap_surjective F K f hf
  let L : Matrix (Fin r) (Fin r) (A ⊗[F] K) := fun i j =>
    Classical.choose (hs (M i j))
  refine ⟨L, ?_⟩
  apply Matrix.ext
  intro i j
  exact Classical.choose_spec (hs (M i j))

/-- The general descent lemma exposes source nilness as a usual explicit
input. The concrete sparse endpoint below supplies that input by its proof. -/
theorem scalarTensorNonUnitalMap_matrix_nil (f : A →ₙₐ[F] B)
    (hf : Function.Surjective f)
    (hsource : ∀ r : ℕ, 0 < r →
      ∀ M : Matrix (Fin r) (Fin r) (A ⊗[F] K), ∃ e : ℕ, positivePower M e = 0) :
    ∀ r : ℕ, 0 < r →
      ∀ M : Matrix (Fin r) (Fin r) (B ⊗[F] K), ∃ e : ℕ, positivePower M e = 0 := by
  intro r hr M
  obtain ⟨L, hL⟩ := scalarTensorNonUnitalMap_matrix_lift F K f hf r M
  obtain ⟨e, he⟩ := hsource r hr L
  have ht := scalarTensorNonUnitalMap_matrix_positivePower F K f r L e
  rw [he, hL] at ht
  refine ⟨e, ht.symm.trans ?_⟩
  apply Matrix.ext
  intro i j
  exact map_zero (scalarTensorNonUnitalMap F K f)

end

noncomputable section

open TensorProduct

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)

/-- The literal scalar extension of the actual positive further-quotient map. -/
def positiveWordIdealScalarFactor (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (hEI : allCutTwoSidedIdeal F W hW ≤ I) :
    (PositiveAllCutQuotient F W hW) ⊗[F] K →ₙₐ[F]
      (PositiveWordIdealQuotient F I hpos) ⊗[F] K :=
  scalarTensorNonUnitalMap F K (positiveWordIdealFactor F I hpos W hW hEI)

theorem positiveWordIdealScalarFactor_surjective (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (hEI : allCutTwoSidedIdeal F W hW ≤ I) :
    Function.Surjective (positiveWordIdealScalarFactor F K I hpos W hW hEI) :=
  scalarTensorNonUnitalMap_surjective F K (positiveWordIdealFactor F I hpos W hW hEI)
    (positiveWordIdealFactor_surjective F I hpos W hW hEI)

/-- Every scalar extension of the same positive quotient is matrix nil. -/
theorem sparse_positiveWordIdeal_scalar_matrix_nil (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ)
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I) :
    ∀ r : ℕ, 0 < r →
      ∀ M : Matrix (Fin r) (Fin r) ((PositiveWordIdealQuotient F I hpos) ⊗[F] K),
        ∃ e : ℕ, positivePower M e = 0 :=
  scalarTensorNonUnitalMap_matrix_nil F K
    (positiveWordIdealFactor F I hpos (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) hEI)
    (positiveWordIdealFactor_surjective F I hpos (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) hEI)
    (sparse_scalar_matrix_nil F K Λ hΛ)

/-- The actual K-unitization of the same scalar-extended new quotient is
algebraic at every matrix order, using its proved actual matrix nilness. -/
theorem sparse_positiveWordIdeal_scalar_unitization_matrix_algebraic (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ)
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I) :
    ∀ r : ℕ, 0 < r → Algebra.IsAlgebraic K
      (Matrix (Fin r) (Fin r) (Unitization K (K ⊗[F] PositiveWordIdealQuotient F I hpos))) :=
  scalarExtension_unitization_matrix_algebraic F K (PositiveWordIdealQuotient F I hpos)
    (sparse_positiveWordIdeal_scalar_matrix_nil F K I hpos Λ hΛ hEI)

#print axioms CriticalGK2.Actual.scalarTensorNonUnitalMapLinear_map_mul
#print axioms CriticalGK2.Actual.positiveWordIdealScalarFactor_surjective
#print axioms CriticalGK2.Actual.sparse_positiveWordIdeal_scalar_matrix_nil
#print axioms CriticalGK2.Actual.sparse_positiveWordIdeal_scalar_unitization_matrix_algebraic

end

end CriticalGK2.Actual
