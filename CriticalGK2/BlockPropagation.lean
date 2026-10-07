import CriticalGK2.ActualBlockPowers

/-!
# Propagation of actual dyadic polynomial block containment

The sole family input is the actual multiplication inclusion at consecutive
levels. It is enough to derive containment of every future actual block in a
power of any earlier block space.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- Actual polynomial block powers preserve genuine subspace inclusions. -/
theorem blockPower_mono {S T : Submodule F (WordAlgebra F)} (hST : S ≤ T) (m : ℕ) :
    blockPower F S m ≤ blockPower F T m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      exact productSpan_mono F ih hST

/-- Multiplication of powers of actual polynomial block spaces flattens to an
actual power of the original space. -/
theorem blockPower_blockPower (S : Submodule F (WordAlgebra F)) (q m : ℕ) :
    blockPower F (blockPower F S q) m = blockPower F S (m * q) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [blockPower_succ, ih, productSpan_blockPower, Nat.succ_mul]

/-- Every future actual block is contained in the full concatenation power of
any chosen earlier block. -/
theorem coherent_family_le_blockPower (S : ℕ → Submodule F (WordAlgebra F))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h)) (H a : ℕ) :
    S (H + a) ≤ blockPower F (S H) (2 ^ a) := by
  induction a with
  | zero => simp
  | succ a ih =>
      calc
        S (H + (a + 1)) ≤ productSpan F (S (H + a)) (S (H + a)) := by
          simpa only [Nat.add_assoc] using hproduct (H + a)
        _ ≤ productSpan F (blockPower F (S H) (2 ^ a))
            (blockPower F (S H) (2 ^ a)) := productSpan_mono F ih ih
        _ = blockPower F (S H) (2 ^ (a + 1)) := by
          rw [productSpan_blockPower]
          congr 1
          rw [pow_succ]
          omega

/-- The same inclusion holds for complete powers of future actual blocks. -/
theorem coherent_family_blockPower_le (S : ℕ → Submodule F (WordAlgebra F))
    (hproduct : ∀ h, S (h + 1) ≤ productSpan F (S h) (S h)) (H a m : ℕ) :
    blockPower F (S (H + a)) m ≤ blockPower F (S H) (m * 2 ^ a) := by
  have h := blockPower_mono F (coherent_family_le_blockPower F S hproduct H a) m
  rw [blockPower_blockPower] at h
  exact h

end

end CriticalGK2.Actual
