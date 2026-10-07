import CriticalGK2.PrefixStages

/-!
# A complete finite dyadic PI segment

All intermediate spaces are actual multiplication powers of the incoming
prefix space. The endpoint is the actual nonzero reset polynomial. The
adjacent-level coherence is proved at every point, including the reset edge.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- Actual homogeneous spaces at relative heights from zero through the
operation height. Only the endpoint uses the reset polynomial. -/
def piSegment (P : PrefixState F) (k a : ℕ) : Submodule F (WordAlgebra F) :=
  if a = operationHeight k then prefixSpace F (resetPrefix F P k).polynomial
  else blockPower F (prefixSpace F P.polynomial) (2 ^ a)

@[simp] theorem piSegment_zero (P : PrefixState F) (k : ℕ) :
    piSegment F P k 0 = prefixSpace F P.polynomial := by
  have h := operationHeight_pos k
  simp [piSegment, Ne.symm (Nat.ne_of_gt h)]

@[simp] theorem piSegment_endpoint (P : PrefixState F) (k : ℕ) :
    piSegment F P k (operationHeight k) =
      prefixSpace F (resetPrefix F P k).polynomial := by
  simp [piSegment]

theorem piSegment_le_homogeneous (P : PrefixState F) (k a : ℕ) :
    piSegment F P k a ≤ homogeneous F (2 ^ (P.height + a)) := by
  by_cases ha : a = operationHeight k
  · subst a
    rw [piSegment_endpoint]
    have h := prefixSpace_le_homogeneous F (resetPrefix F P k).polynomial
      (2 ^ (resetPrefix F P k).height - 1) (resetPrefix F P k).homogeneous
    have hp : 0 < (2 : ℕ) ^ (resetPrefix F P k).height := pow_pos (by norm_num) _
    have hn : 2 ^ (resetPrefix F P k).height - 1 + 1 =
        2 ^ (P.height + operationHeight k) := by
      rw [resetPrefix_height] at hp ⊢
      omega
    simpa only [hn] using h
  · rw [piSegment, if_neg ha]
    have hp : 0 < (2 : ℕ) ^ P.height := pow_pos (by norm_num) _
    have hn : 2 ^ P.height - 1 + 1 = 2 ^ P.height := by omega
    have h := blockPower_le_homogeneous F (prefixSpace F P.polynomial)
      (2 ^ P.height) (by simpa only [hn] using
        prefixSpace_le_homogeneous F P.polynomial _ P.homogeneous) (2 ^ a)
    simpa only [pow_add, Nat.mul_comm] using h

theorem piSegment_ne_bot (P : PrefixState F) (k a : ℕ) :
    piSegment F P k a ≠ ⊥ := by
  by_cases ha : a = operationHeight k
  · subst a
    rw [piSegment_endpoint]
    exact prefixSpace_ne_bot F _ (resetPrefix F P k).nonzero
  · rw [piSegment, if_neg ha]
    exact blockPower_ne_bot F _ (P.polynomial * binaryLetter F false)
      (prefixGenerator_mem F P.polynomial false)
      (mul_ne_zero P.nonzero (binaryLetter_ne_zero F false)) _

/-- Every adjoining pair has block coherence; the final edge follows from
reset containment. -/
theorem piSegment_coherent (P : PrefixState F) (k a : ℕ)
    (ha : a < operationHeight k) :
    piSegment F P k (a + 1) ≤
      productSpan F (piSegment F P k a) (piSegment F P k a) := by
  have hne : a ≠ operationHeight k := Nat.ne_of_lt ha
  simp only [piSegment, if_neg hne]
  have hpow : 2 ^ a + 2 ^ a = (2 : ℕ) ^ (a + 1) := by rw [pow_succ]; omega
  rw [productSpan_blockPower, hpow]
  by_cases he : a + 1 = operationHeight k
  · rw [if_pos he, he]
    exact resetPrefix_space_containment F P k
  · rw [if_neg he]

theorem piSegment_endpoint_killed (C : Type*) [CommRing C] [Algebra F C]
    (P : PrefixState F) (k : ℕ)
    (f : WordAlgebra F →ₐ[F] Matrix (Fin k) (Fin k) C) :
    piSegment F P k (operationHeight k) ≤ LinearMap.ker f.toLinearMap := by
  rw [piSegment_endpoint]
  exact resetPrefix_space_killed F C P k f

end

end CriticalGK2.Actual
