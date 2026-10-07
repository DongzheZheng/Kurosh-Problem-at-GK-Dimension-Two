import CriticalGK2.AutomatonScalarReadback
import CriticalGK2.GenericMatrixDegreeBounds

/-!
# Actual same-field homogeneous readback and finite summation

With coefficient ring equal to the ground field, the actual coefficient
tensor reads under the tensor right-unit equivalence as the actual
homogeneous projection of the actual generic matrix power.  Finite actual
word support then reconstructs the polynomial from those projections.
-/

noncomputable section

namespace CriticalGK2

open TensorProduct

variable {F X : Type*} [Field F] [AddCommGroup X] [Module F X]

/-- Right-unit readback of an actual scalar-extension member is in the
original specified subspace. -/
theorem scalarExtension_rid_mem (D : Submodule F X) (z : X ⊗[F] F)
    (hz : z ∈ scalarExtension D) : TensorProduct.rid F X z ∈ D := by
  obtain ⟨t, rfl⟩ := hz
  have hcomm : TensorProduct.rid F X (D.subtype.rTensor F t) =
      D.subtype (TensorProduct.rid F D t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x c => simp
    | add t t' ht ht' => simp only [map_add, ht, ht']
  rw [hcomm]
  exact (TensorProduct.rid F D t).property

end CriticalGK2

namespace CriticalGK2.Actual

open scoped BigOperators

variable (F : Type*) [Field F]

/-- Actual word-basis coordinates are the original ambient word coefficients. -/
theorem homogeneousWordBasis_repr_apply (n : ℕ) (P : homogeneous F n)
    (w : LengthWord n) : (homogeneousWordBasis F n).repr P w = P.val w.val := by
  classical
  have heq : (homogeneousWordBasis F n).coord w = homogeneousWordCoefficient F n w := by
    apply (homogeneousWordBasis F n).ext
    intro v
    change (homogeneousWordBasis F n).coord w (homogeneousWordBasis F n v) =
      (homogeneousWordBasis F n v).val w.val
    rw [homogeneousWordBasis_coe]
    change (homogeneousWordBasis F n).coord w (homogeneousWordBasis F n v) =
      (Finsupp.single v.val (1 : F)) w.val
    simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply,
      Finsupp.single_apply, Subtype.val_inj, eq_comm]
  simpa only [Module.Basis.coord_apply] using LinearMap.congr_fun heq P

/-- The actual finite set of degrees appearing in a polynomial. -/
def wordDegreeSupport (P : WordAlgebra F) : Finset ℕ :=
  P.support.image FreeMonoid.length

/-- Exact finite reconstruction from actual homogeneous projections. -/
theorem sum_homogeneousProjection_eq (P : WordAlgebra F) :
    (∑ n ∈ wordDegreeSupport F P, (homogeneousProjection F n P).val) = P := by
  classical
  apply Finsupp.ext
  intro w
  rw [Automaton.wordCoefficient_sum]
  simp_rw [homogeneousProjection_coeff]
  by_cases hw : P w = 0
  · simp [hw]
  · have hmem : w.length ∈ wordDegreeSupport F P := by
      exact Finset.mem_image.mpr ⟨w, Finsupp.mem_support_iff.mpr hw, rfl⟩
    simp [hmem, eq_comm]

/-- Membership of every actual same-degree component implies membership of
its finite actual sum in the actual all-cut submodule. -/
theorem mem_allCutSubmodule_of_homogeneousProjections_mem
    (W : DyadicDualData F) (P : WordAlgebra F)
    (hP : ∀ n : ℕ, (homogeneousProjection F n P).val ∈ allCutComponent F W n) :
    P ∈ allCutSubmodule F W := by
  rw [← sum_homogeneousProjection_eq F P]
  exact (allCutSubmodule F W).sum_mem (fun n _ =>
    allCutComponent_le_allCutSubmodule F W n (hP n))

end CriticalGK2.Actual

namespace CriticalGK2.Automaton

open scoped BigOperators
open TensorProduct

variable (F : Type*) [Field F] {r d : ℕ}

/-- The actual tensor right-unit equivalence reconstructs exactly the
actual homogeneous matrix-power coefficient projection. -/
theorem genericPowerTensor_rid (c : Coefficients F r d)
    (n e : ℕ) (a b : Fin r) :
    TensorProduct.rid F (Actual.homogeneous F n) (genericPowerTensor F F c n e a b) =
      Actual.homogeneousProjection F n (((genericMatrix c) ^ e) a b) := by
  classical
  change (TensorProduct.rid F (Actual.homogeneous F n)).toLinearMap
    (genericPowerTensor F F c n e a b) = _
  simp only [genericPowerTensor, map_sum]
  simp only [LinearEquiv.coe_coe, TensorProduct.rid_tmul]
  calc
    (∑ w : Actual.LengthWord n,
      (((genericMatrix c) ^ e) a b) w.val • Actual.homogeneousWordBasis F n w) =
      ∑ w : Actual.LengthWord n,
        (Actual.homogeneousWordBasis F n).repr
          (Actual.homogeneousProjection F n (((genericMatrix c) ^ e) a b)) w •
            Actual.homogeneousWordBasis F n w := by
      apply Finset.sum_congr rfl
      intro w _
      rw [Actual.homogeneousWordBasis_repr_apply, Actual.homogeneousProjection_coeff,
        if_pos w.property]
    _ = Actual.homogeneousProjection F n (((genericMatrix c) ^ e) a b) :=
      (Actual.homogeneousWordBasis F n).sum_repr _

/-- The original actual homogeneous component belongs to the original
specified subspace once its actual annihilator evaluator vanishes. -/
theorem homogeneousProjection_genericPower_mem_of_evaluation_zero
    (c : Coefficients F r d) (hd : 0 < d) (n e : ℕ) (a b : Fin r)
    (D : Submodule F (Actual.homogeneous F n))
    (hzero : ∀ φ : Actual.HomogeneousDual F n, φ ∈ D.dualAnnihilator →
      Actual.actualDualMatrixEvaluation F (Polynomial F) (stateNumber r d) n
        (finiteLetterTransition c) φ = 0) :
    Actual.homogeneousProjection F n (((genericMatrix c) ^ e) a b) ∈ D := by
  have h := CriticalGK2.scalarExtension_rid_mem D
    (genericPowerTensor F F c n e a b)
    (genericPowerTensor_mem_scalarExtension_of_evaluation_zero F F c hd n e a b D hzero)
  rwa [genericPowerTensor_rid] at h

/-- The power's actual homogeneous projection is zero below its exponent. -/
theorem homogeneousProjection_genericPower_eq_zero_of_lt
    (c : Coefficients F r d) (n e : ℕ) (a b : Fin r) (hne : n < e) :
    Actual.homogeneousProjection F n (((genericMatrix c) ^ e) a b) = 0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro w
  rw [Actual.homogeneousProjection_coeff]
  by_cases hw : w.length = n
  · rw [if_pos hw]
    have hwlen : w.toList.length = n := by simpa only [FreeMonoid.length] using hw
    have hz := genericMatrix_pow_coefficient_eq_zero_of_length_lt c e w.toList a b
      (by rw [hwlen]; exact hne)
    simpa only [FreeMonoid.ofList_toList] using hz
  · rw [if_neg hw]
    rfl

#print axioms CriticalGK2.scalarExtension_rid_mem
#print axioms CriticalGK2.Actual.sum_homogeneousProjection_eq
#print axioms CriticalGK2.Automaton.genericPowerTensor_rid
#print axioms CriticalGK2.Automaton.homogeneousProjection_genericPower_mem_of_evaluation_zero

end CriticalGK2.Automaton

end
