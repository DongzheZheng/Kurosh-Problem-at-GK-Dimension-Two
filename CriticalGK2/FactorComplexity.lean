import Mathlib

/-!
# Finite factor complexity forces a periodic tail

The factors here are actual finite windows of an actual one-sided infinite
word over a finite alphabet. Prefix deletion is proved surjective directly.
Equality of consecutive factor counts therefore makes the next letter unique.
Finite pigeonhole and induction then produce a periodic tail.
-/

namespace CriticalGK2.WordLanguage

noncomputable section

variable {α : Type*} [Fintype α]

/-- The actual length-n window beginning at the actual position i. -/
def wordWindow (x : ℕ → α) (n i : ℕ) : Fin n → α :=
  fun j => x (i + j.val)

/-- The actual factors occurring anywhere in the actual infinite word. -/
def Factor (x : ℕ → α) (n : ℕ) : Type _ :=
  {w : Fin n → α // ∃ i : ℕ, wordWindow x n i = w}

instance factorFintype (x : ℕ → α) (n : ℕ) : Fintype (Factor x n) := by
  classical
  change Fintype {w : Fin n → α // ∃ i : ℕ, wordWindow x n i = w}
  infer_instance

/-- A factor with its actual occurrence. -/
def factorAt (x : ℕ → α) (n i : ℕ) : Factor x n :=
  ⟨wordWindow x n i, ⟨i, rfl⟩⟩

/-- Number of actual distinct factors. -/
def factorComplexity (x : ℕ → α) (n : ℕ) : ℕ :=
  Fintype.card (Factor x n)

/-- Prefix deletion on actual occurring factors. -/
def factorPrefix (x : ℕ → α) (n : ℕ) : Factor x (n + 1) → Factor x n := fun w =>
  ⟨fun j => w.val j.castSucc, by
    obtain ⟨i, hi⟩ := w.property
    refine ⟨i, ?_⟩
    funext j
    exact congrFun hi j.castSucc⟩

@[simp]
theorem factorPrefix_factorAt (x : ℕ → α) (n i : ℕ) :
    factorPrefix x n (factorAt x (n + 1) i) = factorAt x n i := by
  apply Subtype.ext
  funext j
  rfl

/-- Every actual factor has an actual right extension in the infinite word. -/
theorem factorPrefix_surjective (x : ℕ → α) (n : ℕ) :
    Function.Surjective (factorPrefix x n) := by
  intro w
  obtain ⟨i, hi⟩ := w.property
  refine ⟨factorAt x (n + 1) i, ?_⟩
  rw [factorPrefix_factorAt]
  exact Subtype.ext hi

/-- Factor complexity is nondecreasing because the actual prefix map is onto. -/
theorem factorComplexity_mono_step (x : ℕ → α) (n : ℕ) :
    factorComplexity x n ≤ factorComplexity x (n + 1) :=
  Fintype.card_le_of_surjective (factorPrefix x n) (factorPrefix_surjective x n)

/-- Equal actual consecutive factor counts give a genuine injective prefix map. -/
theorem factorPrefix_injective_of_equal_complexity (x : ℕ → α) (n : ℕ)
    (hc : factorComplexity x (n + 1) = factorComplexity x n) :
    Function.Injective (factorPrefix x n) :=
  ((Fintype.bijective_iff_surjective_and_card (factorPrefix x n)).mpr
    ⟨factorPrefix_surjective x n, hc⟩).1

/-- Equality of actual n-windows forces equality of their actual complete
(n+1)-windows, including the next letter. -/
theorem wordWindow_succ_eq_of_equal_complexity (x : ℕ → α) (n i j : ℕ)
    (hc : factorComplexity x (n + 1) = factorComplexity x n)
    (hw : wordWindow x n i = wordWindow x n j) :
    wordWindow x (n + 1) i = wordWindow x (n + 1) j := by
  have hp : factorPrefix x n (factorAt x (n + 1) i) =
      factorPrefix x n (factorAt x (n + 1) j) := by
    rw [factorPrefix_factorAt, factorPrefix_factorAt]
    exact Subtype.ext hw
  exact congrArg Subtype.val (factorPrefix_injective_of_equal_complexity x n hc hp)

/-- Dropping the first letter of equal extended windows shifts the equality
one actual position to the right. -/
theorem wordWindow_shift_eq_of_equal_complexity (x : ℕ → α) (n i j : ℕ)
    (hc : factorComplexity x (n + 1) = factorComplexity x n)
    (hw : wordWindow x n i = wordWindow x n j) :
    wordWindow x n (i + 1) = wordWindow x n (j + 1) := by
  have he := wordWindow_succ_eq_of_equal_complexity x n i j hc hw
  funext v
  have hv := congrFun he v.succ
  simpa only [wordWindow, Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv

/-- A repeated actual state continues to repeat at every future position. -/
theorem wordWindow_all_shifts_eq_of_equal_complexity (x : ℕ → α) (n i j : ℕ)
    (hc : factorComplexity x (n + 1) = factorComplexity x n)
    (hw : wordWindow x n i = wordWindow x n j) :
    ∀ t : ℕ, wordWindow x n (i + t) = wordWindow x n (j + t) := by
  intro t
  induction t with
  | zero => simpa only [Nat.add_zero] using hw
  | succ t ih =>
      simpa only [Nat.add_assoc] using
        wordWindow_shift_eq_of_equal_complexity x n (i + t) (j + t) hc ih

/-- Literal eventual periodicity of the original infinite word. -/
def TailPeriodic (x : ℕ → α) : Prop :=
  ∃ i p : ℕ, 0 < p ∧ ∀ t : ℕ, x (i + t + p) = x (i + t)

/-- A repeated positive-length window with unique continuation produces an
actual positive period for the actual original word. -/
theorem tailPeriodic_of_repeated_window (x : ℕ → α) (n i j : ℕ) (hn : 0 < n)
    (hij : i < j) (hc : factorComplexity x (n + 1) = factorComplexity x n)
    (hw : wordWindow x n i = wordWindow x n j) : TailPeriodic x := by
  have hs := wordWindow_all_shifts_eq_of_equal_complexity x n i j hc hw
  refine ⟨i, j - i, by omega, ?_⟩
  intro t
  have hletter : x (i + t) = x (j + t) := by
    simpa only [wordWindow, Nat.add_zero] using congrFun (hs t) (⟨0, hn⟩ : Fin n)
  have hindex : i + t + (j - i) = j + t := by omega
  rw [hindex]
  exact hletter.symm

/-- Finite actual factor states force a repeated positive-length window.
Combined with the proved unique continuation, this gives a periodic tail. -/
theorem tailPeriodic_of_equal_positive_complexity (x : ℕ → α) (n : ℕ) (hn : 0 < n)
    (hc : factorComplexity x (n + 1) = factorComplexity x n) : TailPeriodic x := by
  classical
  let s : Fin (factorComplexity x n + 1) → Factor x n := fun i => factorAt x n i.val
  have hnot : ¬ Function.Injective s :=
    Fintype.not_injective_of_card_lt s (by
      simp only [Fintype.card_fin]
      change factorComplexity x n < factorComplexity x n + 1
      omega)
  simp only [Function.Injective] at hnot
  push_neg at hnot
  obtain ⟨i, j, heq, hne⟩ := hnot
  have hw : wordWindow x n i.val = wordWindow x n j.val := congrArg Subtype.val heq
  have hvals : i.val ≠ j.val := fun h => hne (Fin.ext h)
  by_cases hij : i.val < j.val
  · exact tailPeriodic_of_repeated_window x n i.val j.val hn hij hc hw
  · exact tailPeriodic_of_repeated_window x n j.val i.val hn (by omega) hc hw.symm

/-- The zero-length plateau says directly that every next letter is the same. -/
theorem tailPeriodic_of_equal_zero_complexity (x : ℕ → α)
    (hc : factorComplexity x 1 = factorComplexity x 0) : TailPeriodic x := by
  refine ⟨0, 1, by omega, ?_⟩
  intro t
  have hz : wordWindow x 0 (t + 1) = wordWindow x 0 t := by
    funext j
    exact Fin.elim0 j
  have he := wordWindow_succ_eq_of_equal_complexity x 0 (t + 1) t hc hz
  simpa only [wordWindow, Nat.zero_add, Nat.add_zero] using congrFun he (0 : Fin 1)

/-- Every actual complexity plateau gives a literal periodic tail. -/
theorem tailPeriodic_of_equal_complexity (x : ℕ → α) (n : ℕ)
    (hc : factorComplexity x (n + 1) = factorComplexity x n) : TailPeriodic x := by
  by_cases hn : n = 0
  · subst n
    exact tailPeriodic_of_equal_zero_complexity x hc
  · exact tailPeriodic_of_equal_positive_complexity x n (by omega) hc

/-- A word without a periodic tail has a strict increase at every factor length. -/
theorem factorComplexity_strict_step_of_not_tailPeriodic (x : ℕ → α)
    (haperiodic : ¬ TailPeriodic x) (n : ℕ) :
    factorComplexity x n < factorComplexity x (n + 1) := by
  have hle := factorComplexity_mono_step x n
  by_contra h
  exact haperiodic (tailPeriodic_of_equal_complexity x n (by omega))

instance factorZeroUnique (x : ℕ → α) : Unique (Factor x 0) where
  default := factorAt x 0 0
  uniq w := by
    apply Subtype.ext
    funext j
    exact Fin.elim0 j

@[simp]
theorem factorComplexity_zero (x : ℕ → α) : factorComplexity x 0 = 1 := by
  simp only [factorComplexity, Fintype.card_unique]

/-- The exact finite-alphabet complexity lower bound, proved from actual
factor counting and actual periodicity instead of invoking a word theorem. -/
theorem factorComplexity_ge_length_add_one_of_not_tailPeriodic (x : ℕ → α)
    (haperiodic : ¬ TailPeriodic x) (n : ℕ) : n + 1 ≤ factorComplexity x n := by
  induction n with
  | zero => simp only [factorComplexity_zero]; omega
  | succ n ih =>
      have hs := factorComplexity_strict_step_of_not_tailPeriodic x haperiodic n
      omega

#print axioms CriticalGK2.WordLanguage.factorPrefix_injective_of_equal_complexity
#print axioms CriticalGK2.WordLanguage.tailPeriodic_of_equal_complexity
#print axioms CriticalGK2.WordLanguage.factorComplexity_ge_length_add_one_of_not_tailPeriodic

end

end CriticalGK2.WordLanguage
