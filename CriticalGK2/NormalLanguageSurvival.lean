import CriticalGK2.NormalLanguagePath
import CriticalGK2.NormalWordGreedyBasis

/-!
# Actual normal-word survival and the actual component lower bound

The empty word is normal because its actual quotient image has augmentation
one.  Positive degrees use the already proved actual component survival and
the actual finite greedy word basis.  Thus the every-length path input is
discharged for the same actual sparse quotient.

Distinct occurring stream factors give distinct actual normal-word indices.
The proved greedy cardinality formula then reads the factor-complexity lower
bound as `n+1 <= finrank (H_n/E_n)`.
-/

namespace CriticalGK2.Actual

noncomputable section

open CriticalGK2.Language
open CriticalGK2.WordLanguage

variable (F : Type*) [Field F]

/-- The actual singleton quotient image of the empty word is nonzero, by
the actual descended scalar augmentation. -/
theorem quotientWord_one_ne_zero (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    quotientWord F W hW (1 : Word) ≠ 0 := by
  have haug : allCutQuotientAugmentation F W hW (quotientWord F W hW 1) = 1 := by
    change augmentation F (MonoidAlgebra.single (1 : Word) (1 : F)) = 1
    simp
  intro hzero
  rw [hzero, map_zero] at haug
  exact zero_ne_one haug

/-- No word precedes the empty word in its actual natural-number code. -/
theorem earlierWordImages_one_eq_empty (W : DyadicDualData F)
    (hW : PrimalCoherent F W) : earlierWordImages F W hW (1 : Word) = ∅ := by
  apply Set.ext
  intro z
  constructor
  · intro hz
    obtain ⟨v, _, hcode, _⟩ := hz
    have hnumber : CriticalGK2.WordOrder.wordNumber (1 : Word) = 0 := rfl
    rw [hnumber] at hcode
    exact Nat.not_lt_zero _ hcode
  · intro hz
    exact False.elim hz

/-- The literal empty word is normal in the actual ring quotient. -/
theorem NormalWord_one (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    NormalWord F W hW (1 : Word) := by
  intro hmem
  have hzero : quotientWord F W hW (1 : Word) = 0 := by
    simpa [earlierWordImages_one_eq_empty F W hW] using hmem
  exact quotientWord_one_ne_zero F W hW hzero

/-- Actual root survival gives an actual list normal word at every length,
including the degree-zero word proved separately above. -/
theorem normalWordLanguage_every_length (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (hne : ∀ h : ℕ, W h ≠ ⊥) :
    ∀ n : ℕ, ∃ u : List Bool, u ∈ normalWordLanguage F W hW ∧ u.length = n := by
  intro n
  by_cases hn : n = 0
  · subst n
    exact ⟨[], NormalWord_one F W hW, rfl⟩
  · obtain ⟨w, hw⟩ := exists_normalWord_of_root_ne_bot F W hW n hn
      (hne (strictDyadicRoot n))
    refine ⟨w.val.toList, ?_, w.property⟩
    change NormalWord F W hW (FreeMonoid.ofList w.val.toList)
    rw [FreeMonoid.ofList_toList]
    exact hw

/-- The actual finite word underlying an occurring finite stream factor. -/
def lengthWordOfFactor (x : ℕ → Bool) (n : ℕ) (f : Factor x n) : LengthWord n :=
  ⟨FreeMonoid.ofList (List.ofFn f.val), List.length_ofFn⟩

/-- An occurring factor of a normal-factor stream satisfies the actual
normal criterion for its literal word. -/
theorem lengthWordOfFactor_normal (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (x : ℕ → Bool)
    (hx : ∀ s n : ℕ, streamFactor x s n ∈ normalWordLanguage F W hW)
    (n : ℕ) (f : Factor x n) : NormalWord F W hW (lengthWordOfFactor x n f).val := by
  obtain ⟨i, hi⟩ := f.property
  change NormalWord F W hW (FreeMonoid.ofList (List.ofFn f.val))
  rw [← hi]
  exact hx i n

/-- Actual stream factors map into the actual finite greedy normal indices. -/
def factorToNormalLengthWord (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (x : ℕ → Bool)
    (hx : ∀ s n : ℕ, streamFactor x s n ∈ normalWordLanguage F W hW)
    (n : ℕ) : Factor x n → NormalLengthWord F W hW n := fun f =>
  ⟨lengthWordOfFactor x n f, by
    change quotientWord F W hW (lengthWordOfFactor x n f).val ∉
      Submodule.span F (CriticalGK2.Greedy.Earlier
        (fun v : LengthWord n => quotientWord F W hW v.val)
        (fun v : LengthWord n => CriticalGK2.WordOrder.wordNumber v.val)
        (lengthWordOfFactor x n f))
    rw [greedyEarlier_eq_earlierWordImages]
    exact lengthWordOfFactor_normal F W hW x hx n f⟩

/-- The map records the complete literal factor, hence is injective. -/
theorem factorToNormalLengthWord_injective (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (x : ℕ → Bool)
    (hx : ∀ s n : ℕ, streamFactor x s n ∈ normalWordLanguage F W hW) (n : ℕ) :
    Function.Injective (factorToNormalLengthWord F W hW x hx n) := by
  intro f g hfg
  have hword : FreeMonoid.ofList (List.ofFn f.val) =
      FreeMonoid.ofList (List.ofFn g.val) :=
    congrArg (fun w : NormalLengthWord F W hW n => w.val.val) hfg
  have hlist : List.ofFn f.val = List.ofFn g.val := congrArg FreeMonoid.toList hword
  exact Subtype.ext (List.ofFn_injective hlist)

/-- Actual factor counts are bounded by the actual H_n/E_n dimension,
using the actual greedy basis cardinality equality. -/
theorem factorComplexity_le_componentQuotient_finrank (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (x : ℕ → Bool)
    (hx : ∀ s n : ℕ, streamFactor x s n ∈ normalWordLanguage F W hW) (n : ℕ) :
    factorComplexity x n ≤ Module.finrank F (ComponentQuotient F W n) := by
  have hcard := Fintype.card_le_of_injective (factorToNormalLengthWord F W hW x hx n)
    (factorToNormalLengthWord_injective F W hW x hx n)
  rw [card_normalLengthWord_eq_componentQuotient_finrank F W hW n] at hcard
  exact hcard

/-- The actual sparse quotient has a genuine normal-factor stream, with
the every-length existence input completely supplied by actual survival. -/
theorem sparse_exists_normalWord_stream (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) :
    ∃ x : ℕ → Bool,
      (∀ s n : ℕ, streamFactor x s n ∈ normalWordLanguage F
        (sparseDualData F Λ hΛ) (sparseDualData_primalCoherent F Λ hΛ)) ∧
      (∀ n : ℕ, n + 1 ≤ factorComplexity x n) :=
  sparse_exists_normalWord_stream_of_every_length F Λ hΛ
    (normalWordLanguage_every_length F _ _ (sparseDualData_ne_bot F Λ hΛ))

/-- A linear lower bound in every component of the same sparse quotient. -/
theorem sparse_componentQuotient_finrank_lower (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (n : ℕ) :
    n + 1 ≤ Module.finrank F (ComponentQuotient F (sparseDualData F Λ hΛ) n) := by
  obtain ⟨x, hx, hlower⟩ := sparse_exists_normalWord_stream F Λ hΛ
  exact (hlower n).trans (factorComplexity_le_componentQuotient_finrank F _ _ x hx n)

/-- The component lower bound for the explicitly fixed original-field
construction used by the actual absolute-nil endpoint. -/
theorem originalField_componentQuotient_finrank_lower (n : ℕ) :
    n + 1 ≤ Module.finrank F (ComponentQuotient F
      (sparseDualData F (fun n : ℕ => (n : ℝ)) linearEnvelope_diverges) n) :=
  sparse_componentQuotient_finrank_lower F _ linearEnvelope_diverges n

#print axioms CriticalGK2.Actual.normalWordLanguage_every_length
#print axioms CriticalGK2.Actual.factorComplexity_le_componentQuotient_finrank
#print axioms CriticalGK2.Actual.sparse_componentQuotient_finrank_lower
#print axioms CriticalGK2.Actual.originalField_componentQuotient_finrank_lower

end

end CriticalGK2.Actual
