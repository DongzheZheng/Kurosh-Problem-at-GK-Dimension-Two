import CriticalGK2.HomogeneousCutTensor
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual all-cut quotient dimensions

The quotient is the actual H_n/E_n, the cut factors are the actual homogeneous
completion annihilators, and the tensor maps are the actual concatenation and
degree equivalences. The dimension formula follows from finite sums
and tensor images.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct
open scoped BigOperators

variable (F : Type*) [Field F]

/-- Finite sums of actual subspaces have finrank no larger than the sum of
all their finranks. -/
theorem actual_finrank_finset_sup_le_sum {ι X : Type*} [AddCommGroup X] [Module F X]
    [FiniteDimensional F X] (S : ι → Submodule F X) (t : Finset ι) :
    Module.finrank F ↥(t.sup S) ≤ ∑ i ∈ t, Module.finrank F (S i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      rw [Finset.sup_insert, Finset.sum_insert hi]
      exact (Submodule.finrank_add_le_finrank_add_finrank (S i) (t.sup S)).trans
        (Nat.add_le_add_left ih (Module.finrank F (S i)))

/-- The corresponding actual finite-family supremum bound. -/
theorem actual_finrank_iSup_le_sum {ι X : Type*} [Fintype ι]
    [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    (S : ι → Submodule F X) :
    Module.finrank F ↥(⨆ i, S i : Submodule F X) ≤ ∑ i, Module.finrank F (S i) := by
  classical
  have he : Finset.univ.sup S = (⨆ i, S i : Submodule F X) := by
    apply le_antisymm
    · rw [Finset.sup_eq_iSup]
      exact iSup_le fun i => iSup_le fun _ => le_iSup S i
    · exact iSup_le fun i => Finset.le_sup (Finset.mem_univ i)
  have h := actual_finrank_finset_sup_le_sum F S Finset.univ
  rw [he] at h
  simpa using h

/-- The actual included tensor product has dimension bounded by the product
of the dimensions of the original complete subspaces. -/
theorem actualDualTensorProduct_finrank_le (a b : ℕ)
    (S : Submodule F (HomogeneousDual F a)) (T : Submodule F (HomogeneousDual F b)) :
    Module.finrank F (actualDualTensorProduct F a b S T) ≤
      Module.finrank F S * Module.finrank F T := by
  classical
  letI : FiniteDimensional F (HomogeneousDual F a) :=
    (homogeneousWordBasis F a).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (HomogeneousDual F b) :=
    (homogeneousWordBasis F b).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F S := FiniteDimensional.of_injective S.subtype Subtype.val_injective
  letI : FiniteDimensional F T := FiniteDimensional.of_injective T.subtype Subtype.val_injective
  letI : Module.Free F S := Module.Free.of_basis (Module.Basis.ofVectorSpace F S)
  letI : Module.Free F T := Module.Free.of_basis (Module.Basis.ofVectorSpace F T)
  calc
    Module.finrank F (actualDualTensorProduct F a b S T) =
        Module.finrank F (LinearMap.range
          ((homogeneousDualTensorConcat F a b).toLinearMap.comp
            (TensorProduct.map S.subtype T.subtype))) := by
      rw [actualDualTensorProduct, LinearMap.range_comp]
    _ ≤ Module.finrank F (S ⊗[F] T) :=
      LinearMap.finrank_range_le
        ((homogeneousDualTensorConcat F a b).toLinearMap.comp
          (TensorProduct.map S.subtype T.subtype))
    _ = Module.finrank F S * Module.finrank F T := Module.finrank_tensorProduct

/-- The actual scalar-transported tensor subspace at a literal cut has the
expected upper dimension bound. -/
theorem homogeneousCutDualTensorProduct_finrank_le (W : DyadicDualData F)
    (n : ℕ) (i : Fin (n + 1)) :
    Module.finrank F (homogeneousCutDualTensorProduct F W n i) ≤
      Module.finrank F ((homogeneousLeftCompletion F W i.val).dualAnnihilator) *
      Module.finrank F ((homogeneousRightCompletion F W (n - i.val)).dualAnnihilator) := by
  classical
  letI : FiniteDimensional F (HomogeneousDual F (i.val + (n - i.val))) :=
    (homogeneousWordBasis F (i.val + (n - i.val))).dualBasis.finiteDimensional_of_finite
  let S := (homogeneousLeftCompletion F W i.val).dualAnnihilator
  let T := (homogeneousRightCompletion F W (n - i.val)).dualAnnihilator
  let P := actualDualTensorProduct F i.val (n - i.val) S T
  letI : FiniteDimensional F P := FiniteDimensional.of_injective P.subtype Subtype.val_injective
  change Module.finrank F (P.map
      (homogeneousDualDegreeCast F (homogeneousCutDegree n i)).toLinearMap) ≤ _
  exact (Submodule.finrank_map_le
    (homogeneousDualDegreeCast F (homogeneousCutDegree n i)).toLinearMap P).trans
      (actualDualTensorProduct_finrank_le F i.val (n - i.val) S T)

/-- Finite-dimensional actual word quotients have the same dimension as
annihilators of their exact actual all-cut components. -/
theorem componentQuotient_finrank_eq_dualAnnihilator (W : DyadicDualData F) (n : ℕ) :
    Module.finrank F (ComponentQuotient F W n) =
      Module.finrank F ((homogeneousAllCutComponent F W n).dualAnnihilator) := by
  change Module.finrank F (homogeneous F n ⧸ homogeneousAllCutComponent F W n) = _
  exact (Subspace.quotEquivAnnihilator (homogeneousAllCutComponent F W n)).finrank_eq

/-- The manuscript's cut dimension bound for the literal actual quotient,
including n=0 and both scalar endpoint factors. -/
theorem componentQuotient_finrank_le_cut_sum (W : DyadicDualData F) (n : ℕ) :
    Module.finrank F (ComponentQuotient F W n) ≤
      ∑ i : Fin (n + 1),
        Module.finrank F ((homogeneousLeftCompletion F W i.val).dualAnnihilator) *
        Module.finrank F ((homogeneousRightCompletion F W (n - i.val)).dualAnnihilator) := by
  classical
  letI : FiniteDimensional F (HomogeneousDual F n) :=
    (homogeneousWordBasis F n).dualBasis.finiteDimensional_of_finite
  rw [componentQuotient_finrank_eq_dualAnnihilator,
    homogeneousAllCutComponent_dualAnnihilator_eq_actualTensorCuts]
  exact (actual_finrank_iSup_le_sum F (homogeneousCutDualTensorProduct F W n)).trans
    (Finset.sum_le_sum fun i _ => homogeneousCutDualTensorProduct_finrank_le F W n i)

/-- A uniform bound on both actual complete contraction sides gives the
actual homogeneous quotient bound (n+1)B². -/
theorem componentQuotient_finrank_le_uniform_cut_budget (W : DyadicDualData F) (n B : ℕ)
    (hleft : ∀ i : Fin (n + 1),
      Module.finrank F ((homogeneousLeftCompletion F W i.val).dualAnnihilator) ≤ B)
    (hright : ∀ i : Fin (n + 1),
      Module.finrank F ((homogeneousRightCompletion F W (n - i.val)).dualAnnihilator) ≤ B) :
    Module.finrank F (ComponentQuotient F W n) ≤ (n + 1) * B ^ 2 := by
  calc
    Module.finrank F (ComponentQuotient F W n) ≤
        ∑ i : Fin (n + 1),
          Module.finrank F ((homogeneousLeftCompletion F W i.val).dualAnnihilator) *
          Module.finrank F ((homogeneousRightCompletion F W (n - i.val)).dualAnnihilator) :=
      componentQuotient_finrank_le_cut_sum F W n
    _ ≤ ∑ _i : Fin (n + 1), B * B :=
      Finset.sum_le_sum fun i _ => Nat.mul_le_mul (hleft i) (hright i)
    _ = (n + 1) * B ^ 2 := by simp [Nat.pow_two, Nat.mul_comm]

#print axioms CriticalGK2.Actual.componentQuotient_finrank_le_cut_sum

end

end CriticalGK2.Actual
