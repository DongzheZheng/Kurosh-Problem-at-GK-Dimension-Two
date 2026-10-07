import CriticalGK2.UniformGenericNil
import CriticalGK2.PositiveWordFiltration

/-!
# A single exponent for the actual bounded filtration over every extension

The degree bound refers to the actual positive degree filtration in the
constructed algebra. Every element of that filtration has a positive word
representative with the same degree bound. Tensor induction preserves that
bound over any extension field, and coefficient reading supplies the actual
generic matrix. Thus the generic uniform exponent applies to all matrices
whose entries lie in the scalar extension of the degree-d filtration.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct CriticalGK2.Automaton

variable (F : Type*) [Field F]

/-- Actual degree-d quotient elements have representatives of degree at most d. -/
theorem exists_bounded_positive_word_representative
    (W : DyadicDualData F) (hW : PrimalCoherent F W) (d : ℕ)
    (a : PositiveAllCutQuotient F W hW)
    (ha : a ∈ positiveDegreeFiltration F W hW d) :
    ∃ P : WordAlgebra F, P 1 = 0 ∧
      (∀ w : Word, d < w.length → P w = 0) ∧
      allCutQuotientMap F W hW P = a.val := by
  classical
  rw [positiveDegreeFiltration_eq_wordFiltration] at ha
  change a ∈ Submodule.span F (Set.range (boundedPositiveWordImage F W hW d)) at ha
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · rintro x ⟨w, rfl⟩
    refine ⟨MonoidAlgebra.single w.val 1, ?_, ?_, rfl⟩
    · have hw := boundedPositiveWord_ne_one d w
      simp [MonoidAlgebra.single, Finsupp.single_apply, hw]
    · intro u hu
      have hne : w.val ≠ u := by
        intro he
        have hbound := w.property.2
        rw [he] at hbound
        omega
      simp [MonoidAlgebra.single, Finsupp.single_apply, hne]
  · refine ⟨0, rfl, fun _ _ => rfl, ?_⟩
    exact (allCutQuotientMap F W hW).map_zero
  · intro x y _ _ hx hy
    obtain ⟨P, hP, hPd, hPx⟩ := hx
    obtain ⟨Q, hQ, hQd, hQy⟩ := hy
    refine ⟨P + Q, ?_, ?_, ?_⟩
    · change P 1 + Q 1 = 0
      rw [hP, hQ, add_zero]
    · intro w hw
      change P w + Q w = 0
      rw [hPd w hw, hQd w hw, add_zero]
    · rw [map_add, hPx, hQy]
      rfl
  · intro c x _ hx
    obtain ⟨P, hP, hPd, hPx⟩ := hx
    refine ⟨c • P, ?_, ?_, ?_⟩
    · change c • P 1 = 0
      rw [hP, smul_zero]
    · intro w hw
      change c • P w = 0
      rw [hPd w hw, smul_zero]
    · rw [allCutQuotientMap_smul, hPx]
      rfl

variable (K : Type*) [Field K] [Algebra F K]

/-- The literal scalar extension of the actual degree-d filtration. -/
def positiveScalarDegreeFiltration (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (d : ℕ) :
    Submodule F ((PositiveAllCutQuotient F W hW) ⊗[F] K) :=
  LinearMap.range ((positiveDegreeFiltration F W hW d).subtype.rTensor K)

/-- A scalar-extended bounded element has a literal bounded K-word lift. -/
theorem exists_bounded_positive_scalar_word_representative
    (W : DyadicDualData F) (hW : PrimalCoherent F W) (d : ℕ)
    (z : (PositiveAllCutQuotient F W hW) ⊗[F] K)
    (hz : z ∈ positiveScalarDegreeFiltration F K W hW d) :
    ∃ P : WordAlgebra K, P 1 = 0 ∧
      (∀ w : Word, d < w.length → P w = 0) ∧
      wordScalarQuotientMap F K W hW (coefficientTensorRingEquiv F K P) =
        positiveScalarInclusion F K W hW z := by
  obtain ⟨t, rfl⟩ := hz
  induction t using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, rfl, fun _ _ => rfl, ?_⟩
      rw [LinearMap.map_zero, map_zero, map_zero, map_zero]
  | add t s ht hs =>
      obtain ⟨P, hP, hPd, hPt⟩ := ht
      obtain ⟨Q, hQ, hQd, hQs⟩ := hs
      refine ⟨P + Q, ?_, ?_, ?_⟩
      · change P 1 + Q 1 = 0
        rw [hP, hQ, add_zero]
      · intro w hw
        change P w + Q w = 0
        rw [hPd w hw, hQd w hw, add_zero]
      · rw [map_add, map_add, LinearMap.map_add, map_add, hPt, hQs]
  | tmul a c =>
      obtain ⟨P, hP, hPd, hPa⟩ := exists_bounded_positive_word_representative
        F W hW d a.val a.property
      refine ⟨wordCoefficientTensorEquiv F K (P ⊗ₜ[F] c), ?_, ?_, ?_⟩
      · rw [wordCoefficientTensorEquiv_tmul_coefficient, hP, map_zero, zero_mul]
      · intro w hw
        rw [wordCoefficientTensorEquiv_tmul_coefficient, hPd w hw, map_zero, zero_mul]
      · have hinv : coefficientTensorRingEquiv F K
            (wordCoefficientTensorEquiv F K (P ⊗ₜ[F] c)) = P ⊗ₜ[F] c := by
          change (coefficientTensorRingEquiv F K)
            ((coefficientTensorRingEquiv F K).symm (P ⊗ₜ[F] c)) = _
          exact (coefficientTensorRingEquiv F K).apply_symm_apply _
        rw [hinv, LinearMap.rTensor_tmul, wordScalarQuotientMap_tmul,
          positiveScalarInclusion_tmul, hPa]
        rfl

/-- Every actual bounded scalar matrix is a generic matrix of the same degree. -/
theorem exists_bounded_generic_scalar_matrix_lift
    (W : DyadicDualData F) (hW : PrimalCoherent F W) (r d : ℕ)
    (M : Matrix (Fin r) (Fin r) ((PositiveAllCutQuotient F W hW) ⊗[F] K))
    (hM : ∀ a b, M a b ∈ positiveScalarDegreeFiltration F K W hW d) :
    ∃ c : Coefficients K r d,
      ((genericMatrix c).map (coefficientTensorRingEquiv F K)).map
        (wordScalarQuotientMap F K W hW) = M.map (positiveScalarInclusion F K W hW) := by
  classical
  have hrep := fun a b => exists_bounded_positive_scalar_word_representative
    F K W hW d (M a b) (hM a b)
  let P : Matrix (Fin r) (Fin r) (WordAlgebra K) :=
    fun a b => Classical.choose (hrep a b)
  have hP : ∀ a b, P a b 1 = 0 := fun a b => (Classical.choose_spec (hrep a b)).1
  have hPd : ∀ a b w, d < w.length → P a b w = 0 :=
    fun a b => (Classical.choose_spec (hrep a b)).2.1
  have hsquare : ∀ a b,
      wordScalarQuotientMap F K W hW (coefficientTensorRingEquiv F K (P a b)) =
        positiveScalarInclusion F K W hW (M a b) :=
    fun a b => (Classical.choose_spec (hrep a b)).2.2
  refine ⟨coefficientsFromMatrix (d := d) P, ?_⟩
  rw [genericMatrix_coefficientsFromMatrix P hP hPd]
  exact Matrix.ext hsquare

end

end CriticalGK2.Actual

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct CriticalGK2.Automaton

variable (F : Type*) [Field F]

/-- A uniform exponent for all actual bounded-degree scalar-extended matrices.
The algebra is constructed over F, and the exponent N is uniform over
extension fields K and coefficient choices. Positive-power index N denotes
the usual power N+1. -/
theorem sparse_uniform_bounded_degree_scalar_matrix_nil
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) (r d : ℕ) (hr : 0 < r) (hd : 0 < d) :
    ∃ N : ℕ, ∀ (K : Type*) [Field K] [Algebra F K]
      (M : Matrix (Fin r) (Fin r)
        ((PositiveAllCutQuotient F (sparseDualData F Λ hΛ)
          (sparseDualData_primalCoherent F Λ hΛ)) ⊗[F] K)),
      (∀ a b, M a b ∈ positiveScalarDegreeFiltration F K
        (sparseDualData F Λ hΛ) (sparseDualData_primalCoherent F Λ hΛ) d) →
      positivePower M N = 0 := by
  obtain ⟨N, hN⟩ := sparse_uniform_generic_scalar_matrix_nil F Λ hΛ r d hr hd
  refine ⟨N, ?_⟩
  intro K _ _ M hM
  obtain ⟨c, hc⟩ := exists_bounded_generic_scalar_matrix_lift F K
    (sparseDualData F Λ hΛ) (sparseDualData_primalCoherent F Λ hΛ) r d M hM
  exact hN K c M hc

#print axioms CriticalGK2.Actual.exists_bounded_positive_word_representative
#print axioms CriticalGK2.Actual.exists_bounded_generic_scalar_matrix_lift
#print axioms CriticalGK2.Actual.sparse_uniform_bounded_degree_scalar_matrix_nil

end

end CriticalGK2.Actual
