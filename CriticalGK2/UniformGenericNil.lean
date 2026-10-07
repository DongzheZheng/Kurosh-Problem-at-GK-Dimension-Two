import CriticalGK2.SparseAbsoluteMatrixNil

/-!
# One actual generic nilpotence exponent before all extension fields

The actual sparse all-cut threshold is selected before the coefficient
algebra. Specialization to Polynomial K is performed only after that choice.
Generic power readback absorbs the same positive power
for every coefficient choice in every extension field. Descent gives the same
power for every actual scalar-extended quotient matrix with that literal
generic representative.

The representation equality is explicit. Identifying the image of these
representatives with the scalar extension of the actual degree-d filtration
is proved by the bounded-lifting lemma.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct CriticalGK2.Automaton

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- Generic absorption with a fixed all-cut threshold, keeping its exponent
fixed while the actual generic coefficients vary. -/
theorem generic_wordTensor_positivePower_absorption_of_threshold
    (W : DyadicDualData F) (r d : ℕ) (hd : 0 < d) (N : ℕ)
    (c : Coefficients K r d)
    (hzero : ∀ n : ℕ, N ≤ n →
      (homogeneousAllCutComponent F W n).dualAnnihilator ≤
        LinearMap.ker (actualDualMatrixEvaluation F (Polynomial K) (stateNumber r d) n
          (finiteLetterTransition c))) :
    ∀ a b : Fin r,
      (positivePower ((genericMatrix c).map (coefficientTensorRingEquiv F K)) N) a b ∈
        positiveScalarRelation F K W := by
  intro a b
  have hmem := coefficientTensorMap_genericPower_mem_scalarExtension F K W c hd N (N + 1)
    (Nat.le_succ N) a b (fun n hn phi hphi => hzero n hn hphi)
  have hmap := coefficientTensorRingEquiv_matrix_positivePower F K r (genericMatrix c) N
  have hentry : coefficientTensorMap F K ((positivePower (genericMatrix c) N) a b) =
      (positivePower ((genericMatrix c).map (coefficientTensorRingEquiv F K)) N) a b :=
    congrFun (congrFun hmap a) b
  rw [← positivePower_eq_pow, hentry] at hmem
  exact hmem

end

end CriticalGK2.Actual

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct CriticalGK2.Automaton

variable (F : Type*) [Field F]

/-- One actual positive-power index for a fixed size/degree pair, selected
before every extension field and every generic coefficient choice. Index N
means the usual power N+1. -/
theorem sparse_uniform_generic_scalar_matrix_nil
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) (r d : ℕ) (hr : 0 < r) (hd : 0 < d) :
    ∃ N : ℕ, ∀ (K : Type*) [Field K] [Algebra F K]
      (c : Coefficients K r d)
      (M : Matrix (Fin r) (Fin r)
        ((PositiveAllCutQuotient F (sparseDualData F Λ hΛ)
          (sparseDualData_primalCoherent F Λ hΛ)) ⊗[F] K)),
      ((genericMatrix c).map (coefficientTensorRingEquiv F K)).map
          (wordScalarQuotientMap F K (sparseDualData F Λ hΛ)
            (sparseDualData_primalCoherent F Λ hΛ)) =
        M.map (positiveScalarInclusion F K (sparseDualData F Λ hΛ)
          (sparseDualData_primalCoherent F Λ hΛ)) → positivePower M N = 0 := by
  obtain ⟨N, hN⟩ := sparse_allCut_evaluation_zero F Λ hΛ r d hr hd
  refine ⟨N, ?_⟩
  intro K _ _ c M hmap
  have hE := generic_wordTensor_positivePower_absorption_of_threshold F K
    (sparseDualData F Λ hΛ) r d hd N c
    (fun n hn => hN (Polynomial K) (finiteLetterTransition c) n hn)
  exact positiveScalarMatrixPower_eq_zero_of_lift F K (sparseDualData F Λ hΛ)
    (sparseDualData_primalCoherent F Λ hΛ) r M
    ((genericMatrix c).map (coefficientTensorRingEquiv F K)) hmap N hE

#print axioms CriticalGK2.Actual.generic_wordTensor_positivePower_absorption_of_threshold
#print axioms CriticalGK2.Actual.sparse_uniform_generic_scalar_matrix_nil

end

end CriticalGK2.Actual
