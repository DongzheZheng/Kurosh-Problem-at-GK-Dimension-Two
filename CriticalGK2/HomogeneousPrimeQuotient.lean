import CriticalGK2.InitialDegreeIdeal
import CriticalGK2.HomogeneousQuotientInputs
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Ordinary primeness of the actual maximal homogeneous no-tail quotient

Primeness is stated using all literal ordinary two-sided ideals. The proof
first adjoins I to the two ideals, then takes the actual highest-degree
initial ideals. Their product still lies in I by the actual leading-degree
identity. Strictness forces each initial ideal to contain a full word tail;
their product then contains a word tail, contradicting no-tail.

The final actual ring quotient is H/I, with I chosen above the original
sparse all-cut ideal. It is a unital ring; constructing its positive
non-unital part and transferring the bounds are handled by the positive
quotient theorems.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- Ordinary two-sided primeness of a literal ideal, using all literal
two-sided ideals and their actual products. -/
def WordIdealPrime (I : TwoSidedIdeal (WordAlgebra F)) : Prop :=
  I ≠ ⊤ ∧ ∀ J K : TwoSidedIdeal (WordAlgebra F),
    (∀ P : WordAlgebra F, P ∈ J → ∀ Q : WordAlgebra F, Q ∈ K → P * Q ∈ I) →
    J ≤ I ∨ K ≤ I

/-- Ordinary ring primeness, with no homogeneity restriction on the ideals. -/
def OrdinaryTwoSidedPrime (B : Type*) [Ring B] : Prop :=
  (1 : B) ≠ 0 ∧ ∀ J K : TwoSidedIdeal B,
    (∀ x : B, x ∈ J → ∀ y : B, y ∈ K → x * y = 0) → J = ⊥ ∨ K = ⊥

theorem monomial_mem_wordTailIdeal (N : ℕ) (w : Word) (hw : N ≤ w.length) :
    MonoidAlgebra.single w (1 : F) ∈ wordTailIdeal F N := by
  apply (mem_wordTailIdeal F N _).mpr
  exact Finsupp.single_mem_supported F 1 hw

theorem wordTailIdeal_le_of_tail_products (I J K : TwoSidedIdeal (WordAlgebra F))
    (a b : ℕ) (ha : wordTailIdeal F a ≤ J) (hb : wordTailIdeal F b ≤ K)
    (hprod : ∀ P : WordAlgebra F, P ∈ J → ∀ Q : WordAlgebra F, Q ∈ K → P * Q ∈ I) :
    wordTailIdeal F (a + b) ≤ I := by
  apply wordTailIdeal_le_of_length_monomials F I (a + b)
  intro w
  have hleft : MonoidAlgebra.single (cutLeft a b w).val 1 ∈ J :=
    ha (monomial_mem_wordTailIdeal F a _ (by rw [(cutLeft a b w).property]))
  have hright : MonoidAlgebra.single (cutRight a b w).val 1 ∈ K :=
    hb (monomial_mem_wordTailIdeal F b _ (by rw [(cutRight a b w).property]))
  have hm := hprod _ hleft _ hright
  have hsplit : (cutLeft a b w).val * (cutRight a b w).val = w.val :=
    congrArg Subtype.val (concatenate_cut a b w)
  simpa only [MonoidAlgebra.single_mul_single, one_mul, hsplit] using hm

/-- A maximal homogeneous no-tail ideal is prime for all ordinary ideals. -/
theorem maximal_homogeneous_noWordTail_prime
    (I : TwoSidedIdeal (WordAlgebra F)) (hhom : WordIdealHomogeneous F I)
    (htail : NoWordTail F I)
    (hmax : ∀ J : TwoSidedIdeal (WordAlgebra F), WordIdealHomogeneous F J →
      I < J → ∃ N : ℕ, wordTailIdeal F N ≤ J) : WordIdealPrime F I := by
  classical
  refine ⟨?_, ?_⟩
  · intro htop
    apply htail 0
    rw [htop]
    exact le_top
  · intro J K hprod
    by_cases hJI : J ≤ I
    · exact Or.inl hJI
    by_cases hKI : K ≤ I
    · exact Or.inr hKI
    have hprodSup : ∀ P : WordAlgebra F, P ∈ J ⊔ I →
        ∀ Q : WordAlgebra F, Q ∈ K ⊔ I → P * Q ∈ I := by
      intro P hP Q hQ
      obtain ⟨PJ, hPJ, PI, hPI, hsumP⟩ := TwoSidedIdeal.mem_sup.mp hP
      obtain ⟨QK, hQK, QI, hQI, hsumQ⟩ := TwoSidedIdeal.mem_sup.mp hQ
      rw [← hsumP, ← hsumQ, mul_add, add_mul, add_mul]
      exact I.add_mem
        (I.add_mem (hprod PJ hPJ QK hQK) (I.mul_mem_right PI QK hPI))
        (I.add_mem (I.mul_mem_left PJ QI hQI) (I.mul_mem_left PI QI hQI))
    have hJnot : ¬ J ⊔ I ≤ I := fun h => hJI ((show J ≤ J ⊔ I from le_sup_left).trans h)
    have hKnot : ¬ K ⊔ I ≤ I := fun h => hKI ((show K ≤ K ⊔ I from le_sup_left).trans h)
    have hIJ : I ≤ J ⊔ I := le_sup_right
    have hIK : I ≤ K ⊔ I := le_sup_right
    have hInitialJ : I < initialDegreeIdeal F (J ⊔ I) :=
      lt_of_le_not_ge (le_initialDegreeIdeal F I (J ⊔ I) hhom hIJ)
        (initialDegreeIdeal_not_le_of_not_le F I (J ⊔ I) hIJ hJnot)
    have hInitialK : I < initialDegreeIdeal F (K ⊔ I) :=
      lt_of_le_not_ge (le_initialDegreeIdeal F I (K ⊔ I) hhom hIK)
        (initialDegreeIdeal_not_le_of_not_le F I (K ⊔ I) hIK hKnot)
    obtain ⟨a, ha⟩ := hmax (initialDegreeIdeal F (J ⊔ I))
      (initialDegreeIdeal_homogeneous F (J ⊔ I)) hInitialJ
    obtain ⟨b, hb⟩ := hmax (initialDegreeIdeal F (K ⊔ I))
      (initialDegreeIdeal_homogeneous F (K ⊔ I)) hInitialK
    have htailProd : wordTailIdeal F (a + b) ≤ I :=
      wordTailIdeal_le_of_tail_products F I (initialDegreeIdeal F (J ⊔ I))
        (initialDegreeIdeal F (K ⊔ I)) a b ha hb
        (fun P hP Q hQ => initialDegreeIdeals_mul_mem_of_original_mul_mem F I
          (J ⊔ I) (K ⊔ I) hhom hprodSup P Q hP hQ)
    exact False.elim (htail (a + b) htailProd)

/-- Literal ordinary primeness is transferred to the literal quotient by
actual preimages of all ordinary quotient ideals. -/
theorem wordIdealQuotient_ordinaryPrime (I : TwoSidedIdeal (WordAlgebra F))
    (hI : WordIdealPrime F I) : OrdinaryTwoSidedPrime (WordIdealQuotient F I) := by
  refine ⟨?_, ?_⟩
  · intro hzero
    have hqone : wordIdealQuotientMap F I 1 = 0 := by rw [map_one]; exact hzero
    have hmem := (wordIdealQuotientMap_eq_zero_iff F I 1).mp hqone
    exact hI.1 ((TwoSidedIdeal.one_mem_iff I).mp hmem)
  · intro J K hprod
    let φ := (wordIdealQuotientMap F I).toRingHom
    let J₀ := J.comap φ
    let K₀ := K.comap φ
    have hprod₀ : ∀ P : WordAlgebra F, P ∈ J₀ →
        ∀ Q : WordAlgebra F, Q ∈ K₀ → P * Q ∈ I := by
      intro P hP Q hQ
      apply (wordIdealQuotientMap_eq_zero_iff F I _).mp
      rw [map_mul]
      exact hprod _ hP _ hQ
    rcases hI.2 J₀ K₀ hprod₀ with hJ | hK
    · left
      apply eq_bot_iff.mpr
      intro x hx
      obtain ⟨P, rfl⟩ := wordIdealQuotientMap_surjective F I x
      have hP : P ∈ J₀ := hx
      have hzero := (wordIdealQuotientMap_eq_zero_iff F I P).mpr (hJ hP)
      simpa using hzero
    · right
      apply eq_bot_iff.mpr
      intro x hx
      obtain ⟨P, rfl⟩ := wordIdealQuotientMap_surjective F I x
      have hP : P ∈ K₀ := hx
      have hzero := (wordIdealQuotientMap_eq_zero_iff F I P).mpr (hK hP)
      simpa using hzero

/-- The actual sparse construction has a genuine ordinary-prime homogeneous
further quotient, with infinitude and actual degree lower bounds. -/
theorem sparse_exists_ordinaryPrime_furtherQuotient (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) :
    ∃ I : TwoSidedIdeal (WordAlgebra F),
      allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
        (sparseDualData_primalCoherent F Λ hΛ) ≤ I ∧
      WordIdealHomogeneous F I ∧ NoWordTail F I ∧
      OrdinaryTwoSidedPrime (WordIdealQuotient F I) ∧
      ¬ Module.Finite F (WordIdealQuotient F I) ∧
      (∀ J : TwoSidedIdeal (WordAlgebra F), WordIdealHomogeneous F J → I < J →
        Module.Finite F (WordIdealQuotient F J)) ∧
      (∀ n : ℕ, n + 1 ≤ Module.finrank F
        (CriticalGK2.GenericLower.degreeImage F (wordIdealQuotientMap F I) n)) := by
  obtain ⟨I, hEI, hhom, htail, hinfinite, hfinite, hlower⟩ :=
    sparse_exists_homogeneous_infinite_furtherQuotient F Λ hΛ
  have hmax : ∀ J : TwoSidedIdeal (WordAlgebra F), WordIdealHomogeneous F J →
      I < J → ∃ N : ℕ, wordTailIdeal F N ≤ J := by
    intro J hhomJ hIJ
    exact (wordIdealQuotient_finite_iff_tail F J hhomJ).mp (hfinite J hhomJ hIJ)
  exact ⟨I, hEI, hhom, htail, wordIdealQuotient_ordinaryPrime F I
    (maximal_homogeneous_noWordTail_prime F I hhom htail hmax), hinfinite, hfinite, hlower⟩

#print axioms CriticalGK2.Actual.maximal_homogeneous_noWordTail_prime
#print axioms CriticalGK2.Actual.wordIdealQuotient_ordinaryPrime
#print axioms CriticalGK2.Actual.sparse_exists_ordinaryPrime_furtherQuotient

end

end CriticalGK2.Actual
