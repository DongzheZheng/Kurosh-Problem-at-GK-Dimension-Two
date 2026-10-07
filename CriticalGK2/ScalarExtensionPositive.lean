import CriticalGK2.MatrixQuotientDescent
import CriticalGK2.GradedSurvival
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic

/-!
# Actual scalar extension of the positive non-unital quotient

The tensor product A tensor K has Mathlib's actual non-unital ring multiplication.
Its actual inclusion into B tensor K is injective by ordinary flatness over F.
Finite matrices lift through the actual positive quotient map tensor identity.
An entrywise power in the literal image of E tensor K then descends to zero.

The descent theorem applies when a positive power lies in that tensor image.
-/

namespace CriticalGK2.Actual

open TensorProduct

noncomputable section

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- The actual linear tensor extension of the positive inclusion A into B. -/
def positiveScalarInclusionLinear (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    (PositiveAllCutQuotient F W hW) ⊗[F] K →ₗ[F]
      (AllCutRingQuotient F W hW) ⊗[F] K :=
  (positiveQuotientLinearInclusion F W hW).rTensor K

theorem positiveScalarInclusionLinear_map_mul
    (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (x y : (PositiveAllCutQuotient F W hW) ⊗[F] K) :
    positiveScalarInclusionLinear F K W hW (x * y) =
      positiveScalarInclusionLinear F K W hW x * positiveScalarInclusionLinear F K W hW y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul, LinearMap.map_zero]
  | add x x' hx hx' =>
      simp only [add_mul, LinearMap.map_add, hx, hx']
  | tmul a c =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, LinearMap.map_zero]
      | add y y' hy hy' =>
          simp only [mul_add, LinearMap.map_add, hy, hy']
      | tmul b d =>
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          simp only [positiveScalarInclusionLinear, LinearMap.rTensor_tmul]
          change (a.val * b.val) ⊗ₜ[F] (c * d) =
            (a.val ⊗ₜ[F] c) * (b.val ⊗ₜ[F] d)
          exact (Algebra.TensorProduct.tmul_mul_tmul a.val b.val c d).symm

/-- Literal non-unital algebra inclusion after scalar extension. -/
def positiveScalarInclusion (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    (PositiveAllCutQuotient F W hW) ⊗[F] K →ₙₐ[F]
      (AllCutRingQuotient F W hW) ⊗[F] K where
  toFun := positiveScalarInclusionLinear F K W hW
  map_zero' := (positiveScalarInclusionLinear F K W hW).map_zero
  map_add' := (positiveScalarInclusionLinear F K W hW).map_add
  map_mul' := positiveScalarInclusionLinear_map_mul F K W hW
  map_smul' c x := (positiveScalarInclusionLinear F K W hW).map_smul c x

@[simp]
theorem positiveScalarInclusion_tmul (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (a : PositiveAllCutQuotient F W hW) (c : K) :
    positiveScalarInclusion F K W hW (a ⊗ₜ[F] c) = a.val ⊗ₜ[F] c := rfl

theorem positiveScalarInclusion_injective (W : DyadicDualData F)
    (hW : PrimalCoherent F W) :
    Function.Injective (positiveScalarInclusion F K W hW) := by
  exact Module.Flat.rTensor_preserves_injective_linearMap
    (positiveQuotientLinearInclusion F W hW)
    (fun x y h => Subtype.ext h)

/-- The actual unital word quotient map tensor identity on K. -/
def wordScalarQuotientMap (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    (WordAlgebra F) ⊗[F] K →ₐ[F] (AllCutRingQuotient F W hW) ⊗[F] K :=
  Algebra.TensorProduct.map (allCutQuotientMap F W hW) (AlgHom.id F K)

@[simp]
theorem wordScalarQuotientMap_tmul (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (a : WordAlgebra F) (c : K) :
    wordScalarQuotientMap F K W hW (a ⊗ₜ[F] c) =
      allCutQuotientMap F W hW a ⊗ₜ[F] c := rfl

/-- The literal scalar extension image of the actual all-cut ideal. -/
def positiveScalarRelation (W : DyadicDualData F) : Submodule F ((WordAlgebra F) ⊗[F] K) :=
  LinearMap.range ((allCutSubmodule F W).subtype.rTensor K)

theorem positiveScalarRelation_le_ker (W : DyadicDualData F)
    (hW : PrimalCoherent F W) :
    positiveScalarRelation F K W ≤ (wordScalarQuotientMap F K W hW).toLinearMap.ker := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  change wordScalarQuotientMap F K W hW ((allCutSubmodule F W).subtype.rTensor K t) = 0
  induction t using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, map_zero]
  | add t t' ht ht' =>
      rw [LinearMap.map_add, map_add, ht, ht', add_zero]
  | tmul a c =>
      rw [LinearMap.rTensor_tmul, wordScalarQuotientMap_tmul]
      change allCutQuotientMap F W hW a.val ⊗ₜ[F] c = 0
      rw [(allCutQuotientMap_eq_zero_iff F W hW a.val).mpr a.property, zero_tmul]

/-- The actual positive quotient square commutes after tensoring with K. -/
theorem positiveScalar_quotient_square (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (t : (positiveWordSubmodule F) ⊗[F] K) :
    wordScalarQuotientMap F K W hW ((positiveWordSubmodule F).subtype.rTensor K t) =
      positiveScalarInclusion F K W hW ((positiveAllCutQuotientMap F W hW).rTensor K t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, map_zero, LinearMap.map_zero, map_zero]
  | add t t' ht ht' =>
      rw [LinearMap.map_add, map_add, LinearMap.map_add, map_add, ht, ht']
  | tmul a c =>
      rw [LinearMap.rTensor_tmul, wordScalarQuotientMap_tmul,
        LinearMap.rTensor_tmul, positiveScalarInclusion_tmul]
      all_goals rfl

/-- Every actual scalar-extended A matrix has a literal positive word-tensor lift. -/
theorem exists_positive_scalarMatrix_lift (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (r : ℕ)
    (M : Matrix (Fin r) (Fin r) ((PositiveAllCutQuotient F W hW) ⊗[F] K)) :
    ∃ L : Matrix (Fin r) (Fin r) ((WordAlgebra F) ⊗[F] K),
      (∀ i j, L i j ∈ LinearMap.range ((positiveWordSubmodule F).subtype.rTensor K)) ∧
      L.map (wordScalarQuotientMap F K W hW) = M.map (positiveScalarInclusion F K W hW) := by
  classical
  have hs : Function.Surjective ((positiveAllCutQuotientMap F W hW).rTensor K) :=
    LinearMap.rTensor_surjective K (positiveAllCutQuotientMap_surjective F W hW)
  let t : Fin r → Fin r → (positiveWordSubmodule F) ⊗[F] K := fun i j =>
    Classical.choose (hs (M i j))
  have ht : ∀ i j, (positiveAllCutQuotientMap F W hW).rTensor K (t i j) = M i j := fun i j =>
    Classical.choose_spec (hs (M i j))
  let L : Matrix (Fin r) (Fin r) ((WordAlgebra F) ⊗[F] K) := fun i j =>
    (positiveWordSubmodule F).subtype.rTensor K (t i j)
  refine ⟨L, fun i j => ⟨t i j, rfl⟩, ?_⟩
  apply Matrix.ext
  intro i j
  change wordScalarQuotientMap F K W hW
    ((positiveWordSubmodule F).subtype.rTensor K (t i j)) =
      positiveScalarInclusion F K W hW (M i j)
  rw [positiveScalar_quotient_square, ht]

theorem wordScalarQuotientMap_matrix_positivePower (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (r : ℕ)
    (M : Matrix (Fin r) (Fin r) ((WordAlgebra F) ⊗[F] K)) (e : ℕ) :
    (positivePower M e).map (wordScalarQuotientMap F K W hW) =
      positivePower (M.map (wordScalarQuotientMap F K W hW)) e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [positivePower, Matrix.map_mul, ih]
      rfl

theorem positiveScalarInclusion_matrix_positivePower (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (r : ℕ)
    (M : Matrix (Fin r) (Fin r) ((PositiveAllCutQuotient F W hW) ⊗[F] K)) (e : ℕ) :
    (positivePower M e).map (positiveScalarInclusion F K W hW) =
      positivePower (M.map (positiveScalarInclusion F K W hW)) e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [positivePower, Matrix.map_mul, ih]
      rfl

/-- Actual scalar-extended matrix descent from an actual word-tensor power. -/
theorem positiveScalarMatrixPower_eq_zero_of_lift (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (r : ℕ)
    (M : Matrix (Fin r) (Fin r) ((PositiveAllCutQuotient F W hW) ⊗[F] K))
    (L : Matrix (Fin r) (Fin r) ((WordAlgebra F) ⊗[F] K))
    (hmap : L.map (wordScalarQuotientMap F K W hW) =
      M.map (positiveScalarInclusion F K W hW))
    (e : ℕ) (hE : ∀ i j, (positivePower L e) i j ∈ positiveScalarRelation F K W) :
    positivePower M e = 0 := by
  have hzero : (positivePower L e).map (wordScalarQuotientMap F K W hW) = 0 := by
    apply Matrix.ext
    intro i j
    exact positiveScalarRelation_le_ker F K W hW (hE i j)
  have hA : (positivePower M e).map (positiveScalarInclusion F K W hW) = 0 := by
    rw [positiveScalarInclusion_matrix_positivePower, ← hmap,
      ← wordScalarQuotientMap_matrix_positivePower, hzero]
  apply Matrix.ext
  intro i j
  apply positiveScalarInclusion_injective F K W hW
  change positiveScalarInclusion F K W hW ((positivePower M e) i j) =
    positiveScalarInclusion F K W hW 0
  rw [map_zero]
  exact congrFun (congrFun hA i) j

end

end CriticalGK2.Actual
