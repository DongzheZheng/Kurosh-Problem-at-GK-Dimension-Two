import CriticalGK2.ScalarExtensionPowerReadback
import CriticalGK2.ScalarExtensionPositive
import CriticalGK2.GenericMatrixCoverage
import CriticalGK2.CutDuality

/-!
# Actual scalar-extended quotient matrices: automaton readback and descent

Every positive word tensor has an actual positive K-word image under the
coefficient ring isomorphism.  A finite matrix of those words has an actual
generic representation, obtained from its finite supports.  The already proved
head-coefficient identity, annihilator readback, and finite homogeneous sum
absorb a power into the original actual E tensor K.  The actual quotient
inclusion then descends this power to zero in the actual A tensor K.

The sole construction input is stated as an actual all-cut dual evaluator
vanishing condition. The global sparse construction supplies this condition.
-/

namespace CriticalGK2.Actual

open TensorProduct
open CriticalGK2.Automaton

noncomputable section

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- Scalar extension of the actual positive word submodule consists of
actual K-words with zero empty-word coefficient. -/
theorem wordCoefficientTensorEquiv_positive_constantCoeff
    (z : WordAlgebra F ⊗[F] K)
    (hz : z ∈ LinearMap.range ((positiveWordSubmodule F).subtype.rTensor K)) :
    wordCoefficientTensorEquiv F K z 1 = 0 := by
  obtain ⟨t, rfl⟩ := hz
  induction t using TensorProduct.induction_on with
  | zero =>
      rw [LinearMap.map_zero, LinearEquiv.map_zero]
      rfl
  | add t t' ht ht' =>
      rw [LinearMap.map_add]
      change ((wordCoefficientTensorEquiv F K).toLinearMap
        (((positiveWordSubmodule F).subtype.rTensor K) t +
          ((positiveWordSubmodule F).subtype.rTensor K) t')) 1 = 0
      rw [map_add]
      change wordCoefficientTensorEquiv F K
          (((positiveWordSubmodule F).subtype.rTensor K) t) 1 +
        wordCoefficientTensorEquiv F K
          (((positiveWordSubmodule F).subtype.rTensor K) t') 1 = 0
      rw [ht, ht', add_zero]
  | tmul a c =>
      rw [LinearMap.rTensor_tmul, wordCoefficientTensorEquiv_tmul_coefficient]
      have ha : a.val 1 = 0 :=
        (augmentation_eq_constantCoeff F a.val).symm.trans a.property
      simp only [Submodule.subtype_apply]
      rw [ha, map_zero, zero_mul]

/-- The actual coefficient ring equivalence preserves the actual recursive
positive matrix powers, including in arbitrary characteristic. -/
theorem coefficientTensorRingEquiv_matrix_positivePower (r : ℕ)
    (M : Matrix (Fin r) (Fin r) (WordAlgebra K)) (e : ℕ) :
    (positivePower M e).map (coefficientTensorRingEquiv F K) =
      positivePower (M.map (coefficientTensorRingEquiv F K)) e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [positivePower, Matrix.map_mul, ih]
      rfl

/-- Finite actual positive word-tensor matrices have powers in the literal
scalar extension of E, under the actual all-cut evaluator condition. -/
theorem positive_wordTensorMatrix_power_absorption_of_allCut_evaluation_zero
    (W : DyadicDualData F) (r : ℕ)
    (hzero : ∀ d : ℕ, 0 < d → ∃ N : ℕ,
      ∀ c : Coefficients K r d, ∀ n : ℕ, N ≤ n →
      (homogeneousAllCutComponent F W n).dualAnnihilator ≤
        LinearMap.ker (actualDualMatrixEvaluation F (Polynomial K) (stateNumber r d) n
          (finiteLetterTransition c)))
    (L : Matrix (Fin r) (Fin r) (WordAlgebra F ⊗[F] K))
    (hpositive : ∀ a b,
      L a b ∈ LinearMap.range ((positiveWordSubmodule F).subtype.rTensor K)) :
    ∃ N : ℕ, ∀ a b : Fin r,
      (positivePower L N) a b ∈ positiveScalarRelation F K W := by
  classical
  let P : Matrix (Fin r) (Fin r) (WordAlgebra K) :=
    L.map (coefficientTensorRingEquiv F K).symm
  have hPpositive : ∀ a b, P a b 1 = 0 := by
    intro a b
    exact wordCoefficientTensorEquiv_positive_constantCoeff F K (L a b) (hpositive a b)
  have hPL : P.map (coefficientTensorRingEquiv F K) = L := by
    apply Matrix.ext
    intro a b
    exact (coefficientTensorRingEquiv F K).apply_symm_apply (L a b)
  obtain ⟨d, hd, c, hc⟩ := exists_genericMatrix_representation P hPpositive
  obtain ⟨N, hN⟩ := hzero d hd
  refine ⟨N, ?_⟩
  intro a b
  have hmem := coefficientTensorMap_genericPower_mem_scalarExtension F K W c hd N (N + 1)
    (Nat.le_succ N) a b (fun n hn φ hφ => hN c n hn hφ)
  rw [hc] at hmem
  have hmapPower := coefficientTensorRingEquiv_matrix_positivePower F K r P N
  rw [hPL] at hmapPower
  have hentry : coefficientTensorMap F K ((positivePower P N) a b) =
      (positivePower L N) a b := congrFun (congrFun hmapPower a) b
  rw [← positivePower_eq_pow, hentry] at hmem
  exact hmem

/-- Actual matrix nilness over the actual scalar-extended positive quotient.
The universal evaluator input is the local PI/all-cut output, stated on its
literal actual F-dual spaces and evaluated over Polynomial K. -/
theorem positive_scalar_matrix_nil_of_allCut_evaluation_zero
    (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (hzero : ∀ r : ℕ, 0 < r → ∀ d : ℕ, 0 < d → ∃ N : ℕ,
      ∀ c : Coefficients K r d, ∀ n : ℕ, N ≤ n →
      (homogeneousAllCutComponent F W n).dualAnnihilator ≤
        LinearMap.ker (actualDualMatrixEvaluation F (Polynomial K) (stateNumber r d) n
          (finiteLetterTransition c))) :
    ∀ r : ℕ, 0 < r →
      ∀ M : Matrix (Fin r) (Fin r) ((PositiveAllCutQuotient F W hW) ⊗[F] K),
        ∃ N : ℕ, positivePower M N = 0 := by
  intro r hr M
  obtain ⟨L, hL, hmap⟩ := exists_positive_scalarMatrix_lift F K W hW r M
  obtain ⟨N, hN⟩ := positive_wordTensorMatrix_power_absorption_of_allCut_evaluation_zero
    F K W r (hzero r hr) L hL
  exact ⟨N, positiveScalarMatrixPower_eq_zero_of_lift F K W hW r M L hmap N hN⟩

#print axioms CriticalGK2.Actual.wordCoefficientTensorEquiv_positive_constantCoeff
#print axioms CriticalGK2.Actual.positive_wordTensorMatrix_power_absorption_of_allCut_evaluation_zero
#print axioms CriticalGK2.Actual.positive_scalar_matrix_nil_of_allCut_evaluation_zero

end

end CriticalGK2.Actual
