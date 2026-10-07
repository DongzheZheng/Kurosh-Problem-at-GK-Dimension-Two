import CriticalGK2.PositiveWordIdealFiltration
import CriticalGK2.PositiveWordIdealScalarNil
import CriticalGK2.UniformBoundedDegreeNil

/-!
# Uniform bounded-degree nilness in the actual further positive quotient

The actual quotient homomorphism maps the original degree-d filtration
onto the actual degree-d filtration of H-plus/I. Its restriction is proved
surjective. Tensoring this actual restriction gives degree-preserving lifts
over every extension field. The single original sparse exponent therefore
descends to every matrix in the scalar extension of the new filtration.

The degree condition is on the actual further quotient, and the exponent
is chosen before the extension field and before all matrix coefficients.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)
variable (W : DyadicDualData F) (hW : PrimalCoherent F W)
variable (hEI : allCutTwoSidedIdeal F W hW ≤ I)

/-- The true further quotient map restricted to its actual degree-d spaces. -/
def positiveWordIdealDegreeRestriction (d : ℕ) :
    positiveDegreeFiltration F W hW d →ₗ[F] positiveIdealDegreeFiltration F I hpos d where
  toFun a := ⟨positiveWordIdealFactor F I hpos W hW hEI a.val, by
    rw [positiveIdealFiltration_eq_map F I hpos W hW hEI d]
    exact ⟨a.val, a.property, rfl⟩⟩
  map_add' a b := Subtype.ext
    ((positiveWordIdealFactor F I hpos W hW hEI).map_add' a.val b.val)
  map_smul' c a := Subtype.ext
    ((positiveWordIdealFactor F I hpos W hW hEI).map_smul' c a.val)

/-- Genuine degree-preserving surjectivity, proved from the literal filtration map. -/
theorem positiveWordIdealDegreeRestriction_surjective (d : ℕ) :
    Function.Surjective (positiveWordIdealDegreeRestriction F I hpos W hW hEI d) := by
  intro b
  let bval : PositiveWordIdealQuotient F I hpos := b.val
  have hb : bval ∈ positiveIdealDegreeFiltration F I hpos d := b.property
  rw [positiveIdealFiltration_eq_map F I hpos W hW hEI d] at hb
  obtain ⟨a, ha, hab⟩ := Submodule.mem_map.mp hb
  exact ⟨⟨a, ha⟩, Subtype.ext hab⟩

/-- Literal scalar extension of the actual further quotient's degree-d space. -/
def positiveIdealScalarDegreeFiltration (d : ℕ) :
    Submodule F ((PositiveWordIdealQuotient F I hpos) ⊗[F] K) :=
  LinearMap.range ((positiveIdealDegreeFiltration F I hpos d).subtype.rTensor K)

/-- The actual degree-restricted quotient square commutes after tensoring. -/
theorem positiveWordIdealDegreeRestriction_scalar_square (d : ℕ)
    (t : (positiveDegreeFiltration F W hW d) ⊗[F] K) :
    positiveWordIdealScalarFactor F K I hpos W hW hEI
      ((positiveDegreeFiltration F W hW d).subtype.rTensor K t) =
    (positiveIdealDegreeFiltration F I hpos d).subtype.rTensor K
      ((positiveWordIdealDegreeRestriction F I hpos W hW hEI d).rTensor K t) := by
  change scalarTensorNonUnitalMap F K (positiveWordIdealFactor F I hpos W hW hEI)
      ((positiveDegreeFiltration F W hW d).subtype.rTensor K t) = _
  induction t using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, map_zero, LinearMap.map_zero, LinearMap.map_zero]
  | add t s ht hs =>
      rw [LinearMap.map_add, map_add, LinearMap.map_add, LinearMap.map_add, ht, hs]
  | tmul a c =>
      rw [LinearMap.rTensor_tmul, scalarTensorNonUnitalMap_tmul,
        LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
      rfl

/-- Every bounded scalar-extended new quotient element has an equally bounded
lift through the actual original positive quotient. -/
theorem exists_positiveIdeal_bounded_scalar_lift (d : ℕ)
    (b : (PositiveWordIdealQuotient F I hpos) ⊗[F] K)
    (hb : b ∈ positiveIdealScalarDegreeFiltration F K I hpos d) :
    ∃ a : (PositiveAllCutQuotient F W hW) ⊗[F] K,
      a ∈ positiveScalarDegreeFiltration F K W hW d ∧
      positiveWordIdealScalarFactor F K I hpos W hW hEI a = b := by
  obtain ⟨t, rfl⟩ := hb
  have hs : Function.Surjective
      ((positiveWordIdealDegreeRestriction F I hpos W hW hEI d).rTensor K) :=
    LinearMap.rTensor_surjective K
      (positiveWordIdealDegreeRestriction_surjective F I hpos W hW hEI d)
  obtain ⟨s, hs⟩ := hs t
  refine ⟨(positiveDegreeFiltration F W hW d).subtype.rTensor K s, ⟨s, rfl⟩, ?_⟩
  rw [positiveWordIdealDegreeRestriction_scalar_square, hs]

/-- Actual entrywise degree-preserving lifts of every bounded new quotient matrix. -/
theorem exists_positiveIdeal_bounded_scalar_matrix_lift (r d : ℕ)
    (M : Matrix (Fin r) (Fin r) ((PositiveWordIdealQuotient F I hpos) ⊗[F] K))
    (hM : ∀ a b, M a b ∈ positiveIdealScalarDegreeFiltration F K I hpos d) :
    ∃ L : Matrix (Fin r) (Fin r) ((PositiveAllCutQuotient F W hW) ⊗[F] K),
      (∀ a b, L a b ∈ positiveScalarDegreeFiltration F K W hW d) ∧
      L.map (positiveWordIdealScalarFactor F K I hpos W hW hEI) = M := by
  classical
  have hlift := fun a b => exists_positiveIdeal_bounded_scalar_lift
    F K I hpos W hW hEI d (M a b) (hM a b)
  let L : Matrix (Fin r) (Fin r) ((PositiveAllCutQuotient F W hW) ⊗[F] K) :=
    fun a b => Classical.choose (hlift a b)
  refine ⟨L, fun a b => (Classical.choose_spec (hlift a b)).1, ?_⟩
  apply Matrix.ext
  intro a b
  exact (Classical.choose_spec (hlift a b)).2

end

end CriticalGK2.Actual

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct

variable (F : Type*) [Field F]
variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)

/-- The same actual further quotient has one exponent for each size/degree
pair before every extension field and before every bounded matrix. The
ordinary exponent is N+1 because the non-unital positive-power index is N. -/
theorem sparse_uniform_positiveIdeal_bounded_scalar_matrix_nil
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d) :
    ∃ N : ℕ, ∀ (K : Type*) [Field K] [Algebra F K]
      (M : Matrix (Fin r) (Fin r) ((PositiveWordIdealQuotient F I hpos) ⊗[F] K)),
      (∀ a b, M a b ∈ positiveIdealScalarDegreeFiltration F K I hpos d) →
      positivePower M N = 0 := by
  obtain ⟨N, hN⟩ := sparse_uniform_bounded_degree_scalar_matrix_nil F Λ hΛ r d hr hd
  refine ⟨N, ?_⟩
  intro K _ _ M hM
  obtain ⟨L, hL, hmap⟩ := exists_positiveIdeal_bounded_scalar_matrix_lift F K I hpos
    (sparseDualData F Λ hΛ) (sparseDualData_primalCoherent F Λ hΛ) hEI r d M hM
  have hnil := hN K L hL
  let f := positiveWordIdealFactor F I hpos (sparseDualData F Λ hΛ)
    (sparseDualData_primalCoherent F Λ hΛ) hEI
  have ht := scalarTensorNonUnitalMap_matrix_positivePower F K f r L N
  change L.map (scalarTensorNonUnitalMap F K f) = M at hmap
  rw [hnil, hmap] at ht
  refine ht.symm.trans ?_
  apply Matrix.ext
  intro a b
  exact map_zero (scalarTensorNonUnitalMap F K f)

#print axioms CriticalGK2.Actual.positiveWordIdealDegreeRestriction_surjective
#print axioms CriticalGK2.Actual.exists_positiveIdeal_bounded_scalar_matrix_lift
#print axioms CriticalGK2.Actual.sparse_uniform_positiveIdeal_bounded_scalar_matrix_nil

end

end CriticalGK2.Actual
