import CriticalGK2.NormalWordFactorial
import CriticalGK2.InfiniteWordPath
import CriticalGK2.FactorComplexity
import CriticalGK2.SparseMatrixNil

/-!
# Actual normal words, literal infinite factors, and actual nilness

Factor closure is proved for the normal-word language defined from the actual
quotient word images.  Actual scalar nilness follows from the already proved
one-by-one matrix nil theorem.  It excludes every sufficiently large power of
each nonempty word, and hence excludes a periodic tail for any actual stream
all of whose factors are normal.

The path-existence lemma uses existence of a normal word at every length.
The greedy word basis and degree survival supply these words.
-/

namespace CriticalGK2

noncomputable section

open scoped BigOperators

/-- A matrix constructor for multiplication in the matrix algebra. -/
def finOneMatrix {A : Type*} (a : A) : Matrix (Fin 1) (Fin 1) A :=
  Matrix.of (fun _ _ => a)

@[simp]
theorem finOneMatrix_apply {A : Type*} (a : A) (i j : Fin 1) :
    finOneMatrix a i j = a := rfl

/-- Actual positive powers in a one-by-one matrix are the actual positive
powers of its entry, without adjoining a unit to the entry algebra. -/
theorem finOne_matrix_positivePower {A : Type*} [NonUnitalSemiring A]
    (a : A) (e : ℕ) :
    positivePower (finOneMatrix a) e = finOneMatrix (positivePower a e) := by
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [positivePower, ih]
      apply Matrix.ext
      intro i j
      change (finOneMatrix a * finOneMatrix (positivePower a e)) i j =
        finOneMatrix (positivePower a (e + 1)) i j
      rw [Matrix.mul_apply]
      simp only [finOneMatrix_apply, positivePower, Fin.sum_univ_one]

/-- One-by-one matrix nilness supplies nilness of every actual element. -/
theorem element_positivePower_nil_of_matrix_nil {A : Type*} [NonUnitalSemiring A]
    (hmatrix : ∀ r : ℕ, 0 < r → ∀ M : Matrix (Fin r) (Fin r) A,
      ∃ e : ℕ, positivePower M e = 0) (a : A) :
    ∃ e : ℕ, positivePower a e = 0 := by
  obtain ⟨e, he⟩ := hmatrix 1 (by omega) (finOneMatrix a)
  refine ⟨e, ?_⟩
  have hz : finOneMatrix (positivePower a e) = 0 :=
    (finOne_matrix_positivePower (A := A) a e).symm.trans he
  have hentry := congrArg (fun M : Matrix (Fin 1) (Fin 1) A => M 0 0) hz
  exact hentry

end

end CriticalGK2

namespace CriticalGK2.Language

noncomputable section

/-- The actual factor with a split length is the concatenation of the two
specified actual adjacent factors. -/
theorem streamFactor_add (x : ℕ → Bool) (s a b : ℕ) :
    streamFactor x s (a + b) =
      streamFactor x s a ++ streamFactor x (s + a) b := by
  simpa only [streamFactor, Nat.add_assoc] using
    (List.ofFn_add (f := fun i : Fin (a + b) => x (s + i.val)))

/-- A genuine tail period repeats after every multiple of that period. -/
theorem tailPeriod_multiple (x : ℕ → Bool) (s p : ℕ)
    (hperiod : ∀ t : ℕ, x (s + t + p) = x (s + t)) (e t : ℕ) :
    x (s + t + e * p) = x (s + t) := by
  induction e with
  | zero => simp
  | succ e ih =>
      have hidx : s + t + (e + 1) * p = s + (t + e * p) + p := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [hidx, hperiod]
      simpa only [Nat.add_assoc] using ih

/-- The actual shifted p-block equals the first actual p-block. -/
theorem streamFactor_period_multiple (x : ℕ → Bool) (s p : ℕ)
    (hperiod : ∀ t : ℕ, x (s + t + p) = x (s + t)) (e : ℕ) :
    streamFactor x (s + e * p) p = streamFactor x s p := by
  apply congrArg List.ofFn
  funext j
  have hi : s + e * p + j.val = s + j.val + e * p := by omega
  rw [hi]
  exact tailPeriod_multiple x s p hperiod e j.val

/-- A long actual factor of a periodic tail is a power of its literal first
period word inside the actual free monoid. -/
theorem periodic_streamFactor_word_power (x : ℕ → Bool) (s p : ℕ)
    (hperiod : ∀ t : ℕ, x (s + t + p) = x (s + t)) (e : ℕ) :
    FreeMonoid.ofList (streamFactor x s (e * p)) =
      FreeMonoid.ofList (streamFactor x s p) ^ e := by
  induction e with
  | zero => simp [streamFactor]
  | succ e ih =>
      rw [Nat.succ_mul, streamFactor_add, FreeMonoid.ofList_append, ih,
        streamFactor_period_multiple x s p hperiod e, pow_succ]

end

end CriticalGK2.Language

namespace CriticalGK2.Actual

noncomputable section

open CriticalGK2.Language
open CriticalGK2.WordLanguage

variable (F : Type*) [Field F]

/-- The literal list language of actual quotient normal words. -/
def normalWordLanguage (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    Set (List Bool) := {u | NormalWord F W hW (FreeMonoid.ofList u)}

/-- The actual quotient's normal-word language is factorial. -/
theorem normalWordLanguage_factorClosed (W : DyadicDualData F)
    (hW : PrimalCoherent F W) : FactorClosed (normalWordLanguage F W hW) := by
  intro u v huv hv
  obtain ⟨a, b, rfl⟩ := huv
  apply NormalWord_factor F W hW (FreeMonoid.ofList a) (FreeMonoid.ofList u)
    (FreeMonoid.ofList b)
  simpa only [normalWordLanguage, Set.mem_setOf_eq, FreeMonoid.ofList_append] using hv

/-- The actual positive quotient image of a nonempty actual word. -/
def positiveWordImage (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (u : Word) (hu : u ≠ 1) : PositiveAllCutQuotient F W hW :=
  positiveAllCutQuotientMap F W hW ⟨MonoidAlgebra.single u 1, by
    change augmentation F (MonoidAlgebra.single u 1) = 0
    have hlen : u.length ≠ 0 := fun h => hu (FreeMonoid.length_eq_zero.mp h)
    simp only [augmentation_monomial, if_neg hlen, mul_zero]⟩

@[simp]
theorem positiveWordImage_val (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (u : Word) (hu : u ≠ 1) : (positiveWordImage F W hW u hu).val =
      quotientWord F W hW u := rfl

theorem positiveQuotientInclusion_positivePower (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (a : PositiveAllCutQuotient F W hW) (e : ℕ) :
    positiveQuotientInclusion F W hW (positivePower a e) =
      positivePower (positiveQuotientInclusion F W hW a) e := by
  induction e with
  | zero => rfl
  | succ e ih => rw [positivePower, map_mul, ih]; rfl

theorem quotientWord_pow (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (u : Word) (e : ℕ) : quotientWord F W hW (u ^ e) =
      quotientWord F W hW u ^ e := by
  induction e with
  | zero =>
      simp only [pow_zero, quotientWord, ← MonoidAlgebra.one_def, map_one]
  | succ e ih =>
      simp only [pow_succ, quotientWord_mul, ih]

/-- Nilness of the actual A forbids a positive power of each nonempty
literal word in the actual normal-word language.  The ordinary nilness input
is explicit here and is discharged for the constructed algebra below. -/
theorem normalWord_power_forbidden_of_element_nil (W : DyadicDualData F)
    (hW : PrimalCoherent F W)
    (hnil : ∀ a : PositiveAllCutQuotient F W hW, ∃ e : ℕ, positivePower a e = 0)
    (u : Word) (hu : u ≠ 1) :
    ∃ m : ℕ, 0 < m ∧ ¬ NormalWord F W hW (u ^ m) := by
  obtain ⟨e, he⟩ := hnil (positiveWordImage F W hW u hu)
  have hzero : positivePower (quotientWord F W hW u) e = 0 := by
    have hi : positivePower
        (positiveQuotientInclusion F W hW (positiveWordImage F W hW u hu)) e = 0 := by
      calc
        _ = positiveQuotientInclusion F W hW
            (positivePower (positiveWordImage F W hW u hu) e) :=
          (positiveQuotientInclusion_positivePower F W hW
            (positiveWordImage F W hW u hu) e).symm
        _ = 0 := by rw [he, map_zero]
    have himage : positiveQuotientInclusion F W hW (positiveWordImage F W hW u hu) =
        quotientWord F W hW u := rfl
    rw [himage] at hi
    exact hi
  refine ⟨e + 1, by omega, not_NormalWord_of_quotientWord_eq_zero F W hW _ ?_⟩
  rw [quotientWord_pow, ← positivePower_eq_pow]
  exact hzero

/-- A periodic actual tail contains arbitrarily large powers of a nonempty
literal word, contradicting actual normality and actual nilness. -/
theorem normalWord_stream_not_tailPeriodic (W : DyadicDualData F)
    (hW : PrimalCoherent F W)
    (hnil : ∀ a : PositiveAllCutQuotient F W hW, ∃ e : ℕ, positivePower a e = 0)
    (x : ℕ → Bool)
    (hx : ∀ s n : ℕ, streamFactor x s n ∈ normalWordLanguage F W hW) :
    ¬ TailPeriodic x := by
  rintro ⟨s, p, hp, hperiod⟩
  let u : Word := FreeMonoid.ofList (streamFactor x s p)
  have hu : u ≠ 1 := by
    intro he
    have hlen := congrArg FreeMonoid.length he
    change (streamFactor x s p).length = 0 at hlen
    rw [streamFactor_length] at hlen
    omega
  obtain ⟨m, _, hm⟩ := normalWord_power_forbidden_of_element_nil F W hW hnil u hu
  apply hm
  have hnormal : NormalWord F W hW (FreeMonoid.ofList (streamFactor x s (m * p))) :=
    hx s (m * p)
  rw [periodic_streamFactor_word_power x s p hperiod m] at hnormal
  exact hnormal

/-- The sparse quotient satisfies the normal-language nilness condition. -/
theorem sparse_normalWord_stream_not_tailPeriodic (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (x : ℕ → Bool)
    (hx : ∀ s n : ℕ, streamFactor x s n ∈ normalWordLanguage F
      (sparseDualData F Λ hΛ) (sparseDualData_primalCoherent F Λ hΛ)) :
    ¬ TailPeriodic x :=
  normalWord_stream_not_tailPeriodic F _ _
    (element_positivePower_nil_of_matrix_nil (sparse_positive_matrix_nil F Λ hΛ)) x hx

/-- Path existence remains a visibly conditional lemma until actual greedy
basis and survival prove its every-length input. -/
theorem sparse_exists_normalWord_stream_of_every_length (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ)
    (hwords : ∀ n : ℕ, ∃ u : List Bool,
      u ∈ normalWordLanguage F (sparseDualData F Λ hΛ)
        (sparseDualData_primalCoherent F Λ hΛ) ∧ u.length = n) :
    ∃ x : ℕ → Bool,
      (∀ s n : ℕ, streamFactor x s n ∈ normalWordLanguage F
        (sparseDualData F Λ hΛ) (sparseDualData_primalCoherent F Λ hΛ)) ∧
      (∀ n : ℕ, n + 1 ≤ factorComplexity x n) := by
  obtain ⟨x, hx⟩ := exists_stream_factors_mem _
    (normalWordLanguage_factorClosed F _ _) hwords
  refine ⟨x, hx, ?_⟩
  exact fun n => factorComplexity_ge_length_add_one_of_not_tailPeriodic x
    (sparse_normalWord_stream_not_tailPeriodic F Λ hΛ x hx) n

#print axioms CriticalGK2.Actual.normalWordLanguage_factorClosed
#print axioms CriticalGK2.Actual.normalWord_power_forbidden_of_element_nil
#print axioms CriticalGK2.Actual.sparse_normalWord_stream_not_tailPeriodic
#print axioms CriticalGK2.Actual.sparse_exists_normalWord_stream_of_every_length

end

end CriticalGK2.Actual
