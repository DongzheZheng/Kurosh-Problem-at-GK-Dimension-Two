import CriticalGK2.ActualResidualFinite
import Mathlib.Order.Zorn

/-!
# Actual homogeneous ideals admit maximal quotients without a word tail

The objects are literal two-sided ideals of the original two-letter word
algebra. Homogeneity means closure under each actual coefficient projection.
No word tail means that no actual degree-at-least-N ideal is included.

The finite collection in the chain argument is the set of all actual words
of length N. Their inclusion in one chain member forces the entire word tail
into that member by word splitting.

The final theorem extends an initial homogeneous ideal having no word tail
to a maximal ideal with the same properties. The subsequent quotient and
primeness theorems establish infinite-dimensionality and ordinary primeness.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- Homogeneity of a literal ideal, using the actual degree projections. -/
def WordIdealHomogeneous (I : TwoSidedIdeal (WordAlgebra F)) : Prop :=
  ∀ n : ℕ, ∀ P : WordAlgebra F, P ∈ I → (homogeneousProjection F n P).val ∈ I

/-- A literal ideal contains no full tail of actual words. -/
def NoWordTail (I : TwoSidedIdeal (WordAlgebra F)) : Prop :=
  ∀ N : ℕ, ¬ wordTailIdeal F N ≤ I

/-- Scalar closure is proved from multiplication by the actual scalar image. -/
theorem wordIdeal_smul_mem (I : TwoSidedIdeal (WordAlgebra F))
    (c : F) (P : WordAlgebra F) (hP : P ∈ I) : c • P ∈ I := by
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ _ hP

/-- The actual F-linear subspace underlying any literal two-sided ideal. -/
def wordIdealSubmodule (I : TwoSidedIdeal (WordAlgebra F)) :
    Submodule F (WordAlgebra F) where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := fun hP hQ => I.add_mem hP hQ
  smul_mem' := fun c P hP => wordIdeal_smul_mem F I c P hP

@[simp]
theorem mem_wordIdealSubmodule (I : TwoSidedIdeal (WordAlgebra F))
    (P : WordAlgebra F) : P ∈ wordIdealSubmodule F I ↔ P ∈ I := Iff.rfl

/-- Actual length-N monomials generate the entire actual tail ideal. -/
theorem wordTailIdeal_le_of_length_monomials (I : TwoSidedIdeal (WordAlgebra F))
    (N : ℕ) (hN : ∀ w : LengthWord N, MonoidAlgebra.single w.val 1 ∈ I) :
    wordTailIdeal F N ≤ I := by
  classical
  intro P hP
  have hsupport : ∀ w ∈ P.support, N ≤ w.length := by
    exact (mem_wordTailIdeal F N P).mp hP
  change P ∈ wordIdealSubmodule F I
  change (AlgHom.id F (WordAlgebra F)) P ∈ wordIdealSubmodule F I
  rw [MonoidAlgebra.lift_unique (AlgHom.id F (WordAlgebra F)) P]
  change (∑ w ∈ P.support, P w • MonoidAlgebra.single w 1) ∈ wordIdealSubmodule F I
  apply (wordIdealSubmodule F I).sum_mem
  intro w hw
  apply (wordIdealSubmodule F I).smul_mem
  let v : LengthWord (N + (w.length - N)) :=
    ⟨w, (Nat.add_sub_of_le (hsupport w hw)).symm⟩
  have hsplit :
      (cutLeft N (w.length - N) v).val * (cutRight N (w.length - N) v).val = w :=
    congrArg Subtype.val (concatenate_cut N (w.length - N) v)
  have hm := I.mul_mem_right
    (MonoidAlgebra.single (cutLeft N (w.length - N) v).val 1)
    (MonoidAlgebra.single (cutRight N (w.length - N) v).val 1)
    (hN (cutLeft N (w.length - N) v))
  change MonoidAlgebra.single w (1 : F) ∈ I
  simpa only [MonoidAlgebra.single_mul_single, one_mul, hsplit] using hm

/-- A finite collection of actual vectors contained in a chain union is
contained in one actual chain member. -/
theorem idealChain_contains_finite (c : Set (TwoSidedIdeal (WordAlgebra F)))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (s : Finset (WordAlgebra F))
    (hs : ∀ P ∈ s, ∃ I ∈ c, P ∈ I) :
    ∃ I ∈ c, ∀ P ∈ s, P ∈ I := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty =>
      intro hs
      obtain ⟨I, hI⟩ := hne
      exact ⟨I, hI, by simp⟩
  | @insert P s hPs ih =>
      intro hs
      obtain ⟨I, hI, hsI⟩ := ih (fun Q hQ => hs Q (Finset.mem_insert_of_mem hQ))
      obtain ⟨J, hJ, hPJ⟩ := hs P (Finset.mem_insert_self P s)
      rcases hc.total hI hJ with hIJ | hJI
      · refine ⟨J, hJ, ?_⟩
        intro Q hQ
        rcases Finset.mem_insert.mp hQ with rfl | hQs
        · exact hPJ
        · exact hIJ (hsI Q hQs)
      · refine ⟨I, hI, ?_⟩
        intro Q hQ
        rcases Finset.mem_insert.mp hQ with rfl | hQs
        · exact hJI hPJ
        · exact hsI Q hQs

/-- The literal union ideal of a nonempty chain of literal ideals. -/
def idealChainUnion (c : Set (TwoSidedIdeal (WordAlgebra F)))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) : TwoSidedIdeal (WordAlgebra F) :=
  TwoSidedIdeal.mk' {P | ∃ I ∈ c, P ∈ I}
    (by obtain ⟨I, hI⟩ := hne; exact ⟨I, hI, I.zero_mem⟩)
    (by
      rintro P Q ⟨I, hI, hPI⟩ ⟨J, hJ, hQJ⟩
      rcases hc.total hI hJ with hIJ | hJI
      · exact ⟨J, hJ, J.add_mem (hIJ hPI) hQJ⟩
      · exact ⟨I, hI, I.add_mem hPI (hJI hQJ)⟩)
    (by rintro P ⟨I, hI, hPI⟩; exact ⟨I, hI, I.neg_mem hPI⟩)
    (by rintro P Q ⟨I, hI, hQI⟩; exact ⟨I, hI, I.mul_mem_left P Q hQI⟩)
    (by rintro P Q ⟨I, hI, hPI⟩; exact ⟨I, hI, I.mul_mem_right P Q hPI⟩)

@[simp]
theorem mem_idealChainUnion (c : Set (TwoSidedIdeal (WordAlgebra F)))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) (P : WordAlgebra F) :
    P ∈ idealChainUnion F c hc hne ↔ ∃ I ∈ c, P ∈ I := by
  simp only [idealChainUnion, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq]

theorem le_idealChainUnion (c : Set (TwoSidedIdeal (WordAlgebra F)))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (I : TwoSidedIdeal (WordAlgebra F)) (hI : I ∈ c) : I ≤ idealChainUnion F c hc hne := by
  intro P hP
  exact (mem_idealChainUnion F c hc hne P).mpr ⟨I, hI, hP⟩

theorem idealChainUnion_homogeneous (c : Set (TwoSidedIdeal (WordAlgebra F)))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hhom : ∀ I ∈ c, WordIdealHomogeneous F I) :
    WordIdealHomogeneous F (idealChainUnion F c hc hne) := by
  intro n P hP
  obtain ⟨I, hI, hPI⟩ := (mem_idealChainUnion F c hc hne P).mp hP
  exact (mem_idealChainUnion F c hc hne _).mpr ⟨I, hI, hhom I hI n P hPI⟩

/-- If the actual chain union includes an actual word tail, one actual member
already includes that whole tail. This proves the finite chain obstruction. -/
theorem wordTailIdeal_le_idealChainUnion (c : Set (TwoSidedIdeal (WordAlgebra F)))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) (N : ℕ)
    (hN : wordTailIdeal F N ≤ idealChainUnion F c hc hne) :
    ∃ I ∈ c, wordTailIdeal F N ≤ I := by
  classical
  let s : Finset (WordAlgebra F) :=
    Finset.univ.image (fun w : LengthWord N => MonoidAlgebra.single w.val (1 : F))
  have hs : ∀ P ∈ s, ∃ I ∈ c, P ∈ I := by
    intro P hP
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hP
    apply (mem_idealChainUnion F c hc hne _).mp
    apply hN
    apply (mem_wordTailIdeal F N _).mpr
    change ∀ u ∈ (MonoidAlgebra.single w.val (1 : F)).support, N ≤ u.length
    intro u hu
    have huw : u = w.val := by
      change u ∈ (Finsupp.single w.val (1 : F)).support at hu
      rw [Finsupp.support_single_ne_zero w.val one_ne_zero, Finset.mem_singleton] at hu
      exact hu
    rw [huw, w.property]
  obtain ⟨I, hI, hsI⟩ := idealChain_contains_finite F c hc hne s hs
  refine ⟨I, hI, wordTailIdeal_le_of_length_monomials F I N ?_⟩
  intro w
  exact hsI _ (Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩)

theorem idealChainUnion_noWordTail (c : Set (TwoSidedIdeal (WordAlgebra F)))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (htail : ∀ I ∈ c, NoWordTail F I) : NoWordTail F (idealChainUnion F c hc hne) := by
  intro N hN
  obtain ⟨I, hI, hNI⟩ := wordTailIdeal_le_idealChainUnion F c hc hne N hN
  exact htail I hI N hNI

/-- A literal homogeneous extension with no word tail, maximal among such
extensions. Every strictly larger homogeneous ideal contains an actual tail. -/
theorem exists_maximal_homogeneous_noWordTail
    (I₀ : TwoSidedIdeal (WordAlgebra F))
    (hhom₀ : WordIdealHomogeneous F I₀) (htail₀ : NoWordTail F I₀) :
    ∃ I : TwoSidedIdeal (WordAlgebra F), I₀ ≤ I ∧ WordIdealHomogeneous F I ∧
      NoWordTail F I ∧ ∀ J : TwoSidedIdeal (WordAlgebra F),
        WordIdealHomogeneous F J → I < J → ∃ N : ℕ, wordTailIdeal F N ≤ J := by
  classical
  let S : Set (TwoSidedIdeal (WordAlgebra F)) :=
    {I | I₀ ≤ I ∧ WordIdealHomogeneous F I ∧ NoWordTail F I}
  obtain ⟨I, hI⟩ := zorn_le₀ S (by
    intro c hcs hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨I₀, ⟨le_rfl, hhom₀, htail₀⟩, by simp⟩
    · let U := idealChainUnion F c hc hne
      have hle : I₀ ≤ U := by
        let J : TwoSidedIdeal (WordAlgebra F) := Classical.choose hne
        have hJ : J ∈ c := Classical.choose_spec hne
        exact (hcs hJ).1.trans (le_idealChainUnion F c hc hne J hJ)
      have hhom : WordIdealHomogeneous F U :=
        idealChainUnion_homogeneous F c hc hne (fun J hJ => (hcs hJ).2.1)
      have htail : NoWordTail F U :=
        idealChainUnion_noWordTail F c hc hne (fun J hJ => (hcs hJ).2.2)
      exact ⟨U, ⟨hle, hhom, htail⟩, fun J hJ => le_idealChainUnion F c hc hne J hJ⟩)
  refine ⟨I, hI.prop.1, hI.prop.2.1, hI.prop.2.2, ?_⟩
  intro J hhomJ hIJ
  by_contra htailJ
  have hnoTailJ : NoWordTail F J := by
    intro N hN
    exact htailJ ⟨N, hN⟩
  exact hI.not_prop_of_gt hIJ ⟨hI.prop.1.trans hIJ.le, hhomJ, hnoTailJ⟩

#print axioms CriticalGK2.Actual.wordTailIdeal_le_of_length_monomials
#print axioms CriticalGK2.Actual.wordTailIdeal_le_idealChainUnion
#print axioms CriticalGK2.Actual.idealChainUnion_homogeneous
#print axioms CriticalGK2.Actual.idealChainUnion_noWordTail
#print axioms CriticalGK2.Actual.exists_maximal_homogeneous_noWordTail

end

end CriticalGK2.Actual
