import CriticalGK2.HomogeneousIdealQuotient
import CriticalGK2.GenericNormalLower

/-!
# Actual inputs for normal-word growth after taking a new homogeneous quotient

The new quotient is H/I. Its degree images survive because vanishing of one degree
would force the corresponding full word tail into I. Its nonempty word
images are nil because the actual all-cut quotient factors through H/I.

The last actual-existence statement supplies the initial homogeneity and
no-tail hypotheses of Zorn from the already constructed sparse all-cut ideal.
It gives a genuine infinite homogeneous quotient and its actual component
lower bounds. The highest-degree argument establishes ordinary primeness.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- No full word tail implies survival of every actual homogeneous image. -/
theorem wordIdealQuotient_degreeImage_ne_bot
    (I : TwoSidedIdeal (WordAlgebra F)) (htail : NoWordTail F I) (n : ℕ) :
    CriticalGK2.GenericLower.degreeImage F (wordIdealQuotientMap F I) n ≠ ⊥ := by
  intro hzero
  apply htail n
  apply wordTailIdeal_le_of_length_monomials F I n
  intro w
  apply (wordIdealQuotientMap_eq_zero_iff F I _).mp
  have hmem : wordIdealQuotientMap F I (MonoidAlgebra.single w.val 1) ∈
      CriticalGK2.GenericLower.degreeImage F (wordIdealQuotientMap F I) n :=
    ⟨MonoidAlgebra.single w.val 1, monomial_mem_homogeneous F n w 1, rfl⟩
  rw [hzero] at hmem
  simpa using hmem

/-- Actual factor homomorphism from the actual all-cut ring quotient. -/
def wordIdealFactorFromAllCut (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (I : TwoSidedIdeal (WordAlgebra F)) (hEI : allCutTwoSidedIdeal F W hW ≤ I) :
    AllCutRingQuotient F W hW →ₐ[F] WordIdealQuotient F I :=
  RingCon.factorₐ F (TwoSidedIdeal.ringCon_le_iff.mp hEI)

@[simp]
theorem wordIdealFactorFromAllCut_map (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (I : TwoSidedIdeal (WordAlgebra F)) (hEI : allCutTwoSidedIdeal F W hW ≤ I)
    (P : WordAlgebra F) :
    wordIdealFactorFromAllCut F W hW I hEI (allCutQuotientMap F W hW P) =
      wordIdealQuotientMap F I P := rfl

/-- Nonempty word nilness passes to every further quotient of the
constructed sparse algebra. -/
theorem sparse_furtherQuotient_word_nil (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (I : TwoSidedIdeal (WordAlgebra F))
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I)
    (u : Word) (hu : u ≠ 1) :
    ∃ m : ℕ, 0 < m ∧
      CriticalGK2.GenericLower.wordImage F (wordIdealQuotientMap F I) u ^ m = 0 := by
  let W := sparseDualData F Λ hΛ
  let hW := sparseDualData_primalCoherent F Λ hΛ
  let a := positiveWordImage F W hW u hu
  obtain ⟨e, he⟩ := CriticalGK2.element_positivePower_nil_of_matrix_nil
    (sparse_positive_matrix_nil F Λ hΛ) a
  have hpositive : positivePower (quotientWord F W hW u) e = 0 := by
    have hi : positivePower (positiveQuotientInclusion F W hW a) e = 0 := by
      calc
        _ = positiveQuotientInclusion F W hW (positivePower a e) :=
          (positiveQuotientInclusion_positivePower F W hW a e).symm
        _ = 0 := by rw [he, map_zero]
    have himage : positiveQuotientInclusion F W hW a = quotientWord F W hW u := rfl
    rw [himage] at hi
    exact hi
  have hpower : quotientWord F W hW u ^ (e + 1) = 0 := by
    rw [← positivePower_eq_pow]
    exact hpositive
  let φ := wordIdealFactorFromAllCut F W hW I hEI
  have hword : φ (quotientWord F W hW u) =
      CriticalGK2.GenericLower.wordImage F (wordIdealQuotientMap F I) u := rfl
  refine ⟨e + 1, by omega, ?_⟩
  rw [← hword, ← map_pow, hpower, map_zero]

/-- Actual degree lower bounds hold in the actual further quotient. -/
theorem sparse_furtherQuotient_degree_finrank_lower (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (I : TwoSidedIdeal (WordAlgebra F))
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I)
    (htail : NoWordTail F I) (n : ℕ) :
    n + 1 ≤ Module.finrank F
      (CriticalGK2.GenericLower.degreeImage F (wordIdealQuotientMap F I) n) :=
  CriticalGK2.GenericLower.degreeImage_finrank_lower F (wordIdealQuotientMap F I)
    (wordIdealQuotient_degreeImage_ne_bot F I htail)
    (sparse_furtherQuotient_word_nil F Λ hΛ I hEI) n

theorem allCutWordIdeal_homogeneous (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    WordIdealHomogeneous F (allCutTwoSidedIdeal F W hW) := by
  intro n P hP
  apply (mem_allCutTwoSidedIdeal F W hW _).mpr
  apply allCutComponent_le_allCutSubmodule F W n
  exact homogeneousProjection_allCutSubmodule_mem F W n P
    ((mem_allCutTwoSidedIdeal F W hW P).mp hP)

/-- Actual nonzero roots preclude every full word tail in the actual ideal. -/
theorem allCutWordIdeal_noWordTail (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (hroot : ∀ h : ℕ, W h ≠ ⊥) : NoWordTail F (allCutTwoSidedIdeal F W hW) := by
  intro N hN
  apply allCutComponent_ne_homogeneous F W (N + 1) (by omega)
    (hroot (strictDyadicRoot (N + 1)))
  apply le_antisymm (allCutComponent_le_homogeneous F W (N + 1))
  intro P hP
  have hPT : P ∈ wordTailIdeal F N := by
    apply (mem_wordTailIdeal F N P).mpr
    change ∀ w ∈ P.support, N ≤ w.length
    change ∀ w ∈ P.support, w.length = N + 1 at hP
    intro w hw
    rw [hP w hw]
    omega
  have hPE := (mem_allCutTwoSidedIdeal F W hW P).mp (hN hPT)
  rw [← allCutSubmodule_inf_homogeneous F W (N + 1)]
  exact ⟨hPE, hP⟩

/-- The actual initial hypotheses of Zorn are supplied by the actual sparse
construction. The output is one genuine homogeneous infinite quotient. -/
theorem sparse_exists_homogeneous_infinite_furtherQuotient (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) :
    ∃ I : TwoSidedIdeal (WordAlgebra F),
      allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
        (sparseDualData_primalCoherent F Λ hΛ) ≤ I ∧
      WordIdealHomogeneous F I ∧ NoWordTail F I ∧
      ¬ Module.Finite F (WordIdealQuotient F I) ∧
      (∀ J : TwoSidedIdeal (WordAlgebra F), WordIdealHomogeneous F J → I < J →
        Module.Finite F (WordIdealQuotient F J)) ∧
      (∀ n : ℕ, n + 1 ≤ Module.finrank F
        (CriticalGK2.GenericLower.degreeImage F (wordIdealQuotientMap F I) n)) := by
  let W := sparseDualData F Λ hΛ
  let hW := sparseDualData_primalCoherent F Λ hΛ
  obtain ⟨I, hEI, hhom, htail, hmax⟩ := exists_maximal_homogeneous_noWordTail F
    (allCutTwoSidedIdeal F W hW) (allCutWordIdeal_homogeneous F W hW)
    (allCutWordIdeal_noWordTail F W hW (sparseDualData_ne_bot F Λ hΛ))
  refine ⟨I, hEI, hhom, htail,
    wordIdealQuotient_not_finite_of_noWordTail F I hhom htail, ?_, ?_⟩
  · intro J hhomJ hIJ
    obtain ⟨N, hN⟩ := hmax J hhomJ hIJ
    exact wordIdealQuotient_finite_of_tail F J N hN
  · exact sparse_furtherQuotient_degree_finrank_lower F Λ hΛ I hEI htail

#print axioms CriticalGK2.Actual.wordIdealQuotient_degreeImage_ne_bot
#print axioms CriticalGK2.Actual.sparse_furtherQuotient_word_nil
#print axioms CriticalGK2.Actual.sparse_furtherQuotient_degree_finrank_lower
#print axioms CriticalGK2.Actual.sparse_exists_homogeneous_infinite_furtherQuotient

end

end CriticalGK2.Actual
