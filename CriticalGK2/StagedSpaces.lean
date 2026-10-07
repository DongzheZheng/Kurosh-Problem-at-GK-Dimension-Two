import CriticalGK2.PISegment

/-!
# Waiting and PI segments assembled by actual polynomial recursion

The waiting counts and matrix sizes are arbitrary natural-number sequences.
The constructed prefixes, intermediate spaces, degree bounds, survival and
all adjacent coherence edges are derived from the concrete transitions.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

def waitIter (P : PrefixState F) : ℕ → PrefixState F
  | 0 => P
  | a + 1 => waitPrefix F (waitIter P a)

@[simp] theorem waitIter_zero (P : PrefixState F) : waitIter F P 0 = P := rfl
@[simp] theorem waitIter_succ (P : PrefixState F) (a : ℕ) :
    waitIter F P (a + 1) = waitPrefix F (waitIter F P a) := rfl

@[simp] theorem waitIter_height (P : PrefixState F) (a : ℕ) :
    (waitIter F P a).height = P.height + a := by
  induction a with
  | zero => simp
  | succ a ih => simp only [waitIter_succ, waitPrefix_height, ih, Nat.add_assoc]

def stageSpace (P : PrefixState F) (k w a : ℕ) : Submodule F (WordAlgebra F) :=
  if a ≤ w then prefixSpace F (waitIter F P a).polynomial
  else piSegment F (waitIter F P w) k (a - w)

@[simp] theorem stageSpace_zero (P : PrefixState F) (k w : ℕ) :
    stageSpace F P k w 0 = prefixSpace F P.polynomial := by simp [stageSpace]

theorem stageSpace_le_homogeneous (P : PrefixState F) (k w a : ℕ) :
    stageSpace F P k w a ≤ homogeneous F (2 ^ (P.height + a)) := by
  by_cases ha : a ≤ w
  · rw [stageSpace, if_pos ha]
    let Q := waitIter F P a
    have h := prefixSpace_le_homogeneous F Q.polynomial (2 ^ Q.height - 1) Q.homogeneous
    have hp : 0 < (2 : ℕ) ^ Q.height := pow_pos (by norm_num) _
    have hn : 2 ^ Q.height - 1 + 1 = 2 ^ Q.height := by omega
    rw [hn] at h
    simpa only [Q, waitIter_height] using h
  · rw [stageSpace, if_neg ha]
    have hn : (waitIter F P w).height + (a - w) = P.height + a := by
      rw [waitIter_height]
      omega
    simpa only [hn] using piSegment_le_homogeneous F (waitIter F P w) k (a - w)

theorem stageSpace_ne_bot (P : PrefixState F) (k w a : ℕ) :
    stageSpace F P k w a ≠ ⊥ := by
  by_cases ha : a ≤ w
  · rw [stageSpace, if_pos ha]
    exact prefixSpace_ne_bot F _ (waitIter F P a).nonzero
  · rw [stageSpace, if_neg ha]
    exact piSegment_ne_bot F _ _ _

theorem stageSpace_endpoint (P : PrefixState F) (k w : ℕ) :
    stageSpace F P k w (w + operationHeight k) =
      prefixSpace F (resetPrefix F (waitIter F P w) k).polynomial := by
  have hs := operationHeight_pos k
  have hn : ¬ w + operationHeight k ≤ w := by omega
  simp only [stageSpace, if_neg hn, Nat.add_sub_cancel_left, piSegment_endpoint]

theorem stageSpace_coherent (P : PrefixState F) (k w a : ℕ)
    (ha : a < w + operationHeight k) :
    stageSpace F P k w (a + 1) ≤
      productSpan F (stageSpace F P k w a) (stageSpace F P k w a) := by
  by_cases hlt : a < w
  · have ha0 : a ≤ w := by omega
    have ha1 : a + 1 ≤ w := by omega
    simp only [stageSpace, if_pos ha0, if_pos ha1, waitIter_succ]
    exact waitPrefix_space_coherent F (waitIter F P a)
  · by_cases he : a = w
    · subst a
      have hnext : ¬ w + 1 ≤ w := by omega
      simp only [stageSpace, if_pos le_rfl, if_neg hnext, Nat.add_sub_cancel_left]
      have h := piSegment_coherent F (waitIter F P w) k 0 (operationHeight_pos k)
      simpa only [piSegment_zero, Nat.zero_add] using h
    · have ha0 : ¬ a ≤ w := by omega
      have ha1 : ¬ a + 1 ≤ w := by omega
      have hage : a - w < operationHeight k := by omega
      have hsucc : a + 1 - w = (a - w) + 1 := by omega
      simp only [stageSpace, if_neg ha0, if_neg ha1, hsucc]
      exact piSegment_coherent F _ _ _ hage

def stagePrefix (waiting size : ℕ → ℕ) : ℕ → PrefixState F
  | 0 => initialPrefix F
  | j + 1 => resetPrefix F (waitIter F (stagePrefix waiting size j) (waiting j)) (size j)

def stageHeight (waiting size : ℕ → ℕ) (j : ℕ) : ℕ :=
  (stagePrefix F waiting size j).height

@[simp] theorem stageHeight_zero (waiting size : ℕ → ℕ) :
    stageHeight F waiting size 0 = 0 := rfl

@[simp] theorem stageHeight_succ (waiting size : ℕ → ℕ) (j : ℕ) :
    stageHeight F waiting size (j + 1) =
      stageHeight F waiting size j + waiting j + operationHeight (size j) := by
  simp only [stageHeight, stagePrefix, resetPrefix_height, waitIter_height]

theorem stageHeight_lt_succ (waiting size : ℕ → ℕ) (j : ℕ) :
    stageHeight F waiting size j < stageHeight F waiting size (j + 1) := by
  rw [stageHeight_succ]
  have hs := operationHeight_pos (size j)
  omega

theorem stageHeight_strictMono (waiting size : ℕ → ℕ) :
    StrictMono (stageHeight F waiting size) :=
  strictMono_nat_of_lt_succ (stageHeight_lt_succ F waiting size)

theorem index_le_stageHeight (waiting size : ℕ → ℕ) (j : ℕ) :
    j ≤ stageHeight F waiting size j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := stageHeight_lt_succ F waiting size j
    omega

theorem stageSpace_matches_next (waiting size : ℕ → ℕ) (j : ℕ) :
    stageSpace F (stagePrefix F waiting size j) (size j) (waiting j)
        (waiting j + operationHeight (size j)) =
      stageSpace F (stagePrefix F waiting size (j + 1)) (size (j + 1))
        (waiting (j + 1)) 0 := by
  rw [stageSpace_endpoint, stageSpace_zero]
  rfl

end

end CriticalGK2.Actual
