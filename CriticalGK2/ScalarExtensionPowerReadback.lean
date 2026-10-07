import CriticalGK2.ScalarWordTensor
import CriticalGK2.SameFieldReadback

/-!
# Actual extension-field power absorption

Each actual homogeneous coefficient tensor of a generic matrix over K is
sent into the original ambient scalar extension.  The coefficient-ring
word isomorphism and the finite actual homogeneous decomposition identify
the sum with the actual K-word matrix power.  Thus eventual vanishing of
the actual F-dual all-cut evaluator gives actual power membership in E⊗K.
The evaluator-vanishing input is explicit and is supplied separately by
the universal local PI and the constructed all-cut spaces.
-/

namespace CriticalGK2

open TensorProduct

noncomputable section

variable {F X Y K : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]

/-- Actual tensorized subspaces are functorial under an actual linear map. -/
theorem scalarExtension_linearMap_mem (D : Submodule F X) (E : Submodule F Y)
    (f : X →ₗ[F] Y) (hDE : D ≤ E.comap f) (z : X ⊗[F] K)
    (hz : z ∈ scalarExtension D) : f.rTensor K z ∈ scalarExtension E := by
  obtain ⟨t, rfl⟩ := hz
  let g : D →ₗ[F] E :=
    { toFun := fun x => ⟨f x.val, hDE x.property⟩
      map_add' := fun x y => Subtype.ext (f.map_add x.val y.val)
      map_smul' := fun a x => Subtype.ext (f.map_smul a x.val) }
  have heq : E.subtype.comp g = f.comp D.subtype := by ext x; rfl
  refine ⟨g.rTensor K t, ?_⟩
  rw [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply, heq]

end

end CriticalGK2

namespace CriticalGK2.Automaton

open scoped BigOperators
open TensorProduct

noncomputable section

variable (F K : Type*) [Field F] [Field K] [Algebra F K] {r d : ℕ}

/-- The actual degree-n power tensor included in the original ambient tensor space. -/
def genericPowerAmbientTensor (c : Coefficients K r d) (n e : ℕ) (a b : Fin r) :
    Actual.WordAlgebra F ⊗[F] K :=
  (Actual.homogeneous F n).subtype.rTensor K (genericPowerTensor F K c n e a b)

/-- Its actual K-word image is exactly the actual degree-n coefficient projection. -/
theorem genericPowerAmbientTensor_projection (c : Coefficients K r d)
    (n e : ℕ) (a b : Fin r) :
    Actual.wordCoefficientTensorEquiv F K (genericPowerAmbientTensor F K c n e a b) =
      (Actual.homogeneousProjection K n (((genericMatrix c) ^ e) a b)).val := by
  classical
  let P : Actual.WordAlgebra K := ((genericMatrix c) ^ e) a b
  have hleft :
      ((Actual.wordCoefficientTensorEquiv F K).toLinearMap.comp
        ((Actual.homogeneous F n).subtype.rTensor K)) (genericPowerTensor F K c n e a b) =
      ∑ w : Actual.LengthWord n, P w.val • (Actual.homogeneousWordBasis K n w).val := by
    rw [genericPowerTensor, map_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply,
      Actual.homogeneousWordBasis_coe]
    change Actual.wordCoefficientTensorEquiv F K
      (MonoidAlgebra.single w.val (1 : F) ⊗ₜ[F] P w.val) =
        P w.val • MonoidAlgebra.single w.val (1 : K)
    rw [Actual.wordCoefficientTensorEquiv_single_tmul]
    change (Finsupp.single w.val (P w.val)) = P w.val • (Finsupp.single w.val (1 : K))
    simp [Finsupp.smul_single]
  have hsum : (∑ w : Actual.LengthWord n,
      P w.val • Actual.homogeneousWordBasis K n w) = Actual.homogeneousProjection K n P := by
    calc
      (∑ w : Actual.LengthWord n, P w.val • Actual.homogeneousWordBasis K n w) =
        ∑ w : Actual.LengthWord n,
          (Actual.homogeneousWordBasis K n).repr (Actual.homogeneousProjection K n P) w •
            Actual.homogeneousWordBasis K n w := by
        apply Finset.sum_congr rfl
        intro w _
        rw [Actual.homogeneousWordBasis_repr_apply, Actual.homogeneousProjection_coeff,
          if_pos w.property]
      _ = Actual.homogeneousProjection K n P := (Actual.homogeneousWordBasis K n).sum_repr _
  have hval := congrArg (fun x : Actual.homogeneous K n => x.val) hsum
  change (Actual.homogeneous K n).subtype
      (∑ w : Actual.LengthWord n, P w.val • Actual.homogeneousWordBasis K n w) = _ at hval
  rw [map_sum] at hval
  simp only [map_smul] at hval
  exact hleft.trans hval

/-- An actual homogeneous scalar-extension member lands in the actual
ambient scalar extension of E. -/
theorem genericPowerAmbientTensor_mem_of_evaluation_zero
    (W : Actual.DyadicDualData F) (c : Coefficients K r d) (hd : 0 < d)
    (n e : ℕ) (a b : Fin r)
    (hzero : ∀ φ : Actual.HomogeneousDual F n,
      φ ∈ ((Actual.allCutComponent F W n).comap (Actual.homogeneous F n).subtype).dualAnnihilator →
      Actual.actualDualMatrixEvaluation F (Polynomial K) (stateNumber r d) n
        (finiteLetterTransition c) φ = 0) :
    genericPowerAmbientTensor F K c n e a b ∈
      CriticalGK2.scalarExtension (Actual.allCutSubmodule F W) := by
  let D := (Actual.allCutComponent F W n).comap (Actual.homogeneous F n).subtype
  have hD : D ≤ (Actual.allCutSubmodule F W).comap (Actual.homogeneous F n).subtype := by
    intro x hx
    exact Actual.allCutComponent_le_allCutSubmodule F W n hx
  exact CriticalGK2.scalarExtension_linearMap_mem (F := F) (K := K)
    (X := Actual.homogeneous F n) (Y := Actual.WordAlgebra F)
    D (Actual.allCutSubmodule F W)
    (Actual.homogeneous F n).subtype hD (genericPowerTensor F K c n e a b)
    (genericPowerTensor_mem_scalarExtension_of_evaluation_zero F K c hd n e a b D hzero)

/-- The actual homogeneous coefficient tensor vanishes below the exponent,
including before passage to any quotient. -/
theorem genericPowerTensor_eq_zero_of_lt (c : Coefficients K r d)
    (n e : ℕ) (a b : Fin r) (hne : n < e) :
    genericPowerTensor F K c n e a b = 0 := by
  classical
  unfold genericPowerTensor
  apply Finset.sum_eq_zero
  intro w _
  have hwlen : w.val.toList.length = n := by simpa only [FreeMonoid.length] using w.property
  have hz := genericMatrix_pow_coefficient_eq_zero_of_length_lt c e w.val.toList a b
    (by rw [hwlen]; exact hne)
  have hcoeff : (((genericMatrix c) ^ e) a b) w.val = 0 := by
    simpa only [FreeMonoid.ofList_toList] using hz
  rw [hcoeff]
  simp only [TensorProduct.tmul_zero]

/-- Exact finite decomposition of the actual K-word power after the actual
noncommutative coefficient tensor isomorphism. -/
theorem coefficientTensorMap_genericPower_decomposition (c : Coefficients K r d)
    (e : ℕ) (a b : Fin r) :
    Actual.coefficientTensorMap F K (((genericMatrix c) ^ e) a b) =
      ∑ n ∈ Actual.wordDegreeSupport K (((genericMatrix c) ^ e) a b),
        genericPowerAmbientTensor F K c n e a b := by
  classical
  apply (Actual.wordCoefficientTensorEquiv F K).injective
  change (Actual.wordCoefficientTensorEquiv F K).toLinearMap
      (Actual.coefficientTensorMap F K (((genericMatrix c) ^ e) a b)) =
    (Actual.wordCoefficientTensorEquiv F K).toLinearMap
      (∑ n ∈ Actual.wordDegreeSupport K (((genericMatrix c) ^ e) a b),
        genericPowerAmbientTensor F K c n e a b)
  rw [map_sum]
  simp only [LinearEquiv.coe_coe, Actual.coefficientTensorMap,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, genericPowerAmbientTensor_projection]
  exact (Actual.sum_homogeneousProjection_eq K (((genericMatrix c) ^ e) a b)).symm

/-- Eventual vanishing of the actual original F-dual evaluator absorbs an
actual K-word power into the actual scalar extension of E. -/
theorem coefficientTensorMap_genericPower_mem_scalarExtension
    (W : Actual.DyadicDualData F) (c : Coefficients K r d) (hd : 0 < d)
    (N e : ℕ) (he : N ≤ e) (a b : Fin r)
    (hzero : ∀ n : ℕ, N ≤ n → ∀ φ : Actual.HomogeneousDual F n,
      φ ∈ ((Actual.allCutComponent F W n).comap (Actual.homogeneous F n).subtype).dualAnnihilator →
      Actual.actualDualMatrixEvaluation F (Polynomial K) (stateNumber r d) n
        (finiteLetterTransition c) φ = 0) :
    Actual.coefficientTensorMap F K (((genericMatrix c) ^ e) a b) ∈
      CriticalGK2.scalarExtension (Actual.allCutSubmodule F W) := by
  classical
  rw [coefficientTensorMap_genericPower_decomposition]
  apply (CriticalGK2.scalarExtension (Actual.allCutSubmodule F W)).sum_mem
  intro n _
  by_cases hn : n < e
  · rw [genericPowerAmbientTensor, genericPowerTensor_eq_zero_of_lt F K c n e a b hn, map_zero]
    exact Submodule.zero_mem _
  · exact genericPowerAmbientTensor_mem_of_evaluation_zero F K W c hd n e a b
      (hzero n (he.trans (by omega)))

#print axioms CriticalGK2.scalarExtension_linearMap_mem
#print axioms CriticalGK2.Automaton.genericPowerAmbientTensor_projection
#print axioms CriticalGK2.Automaton.coefficientTensorMap_genericPower_mem_scalarExtension

end

end CriticalGK2.Automaton
