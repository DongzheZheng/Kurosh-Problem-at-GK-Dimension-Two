import CriticalGK2.ActualWordCutRank

/-!
# Intrinsic actual polynomial cut budget and waiting invariance

The budget here is a finite maximum of ranks of honest contractions of the
actual coefficient tensor. It is computed from a polynomial. Every cut of `P*x*P` is placed inside the first or the second
copy of `P`; the actual fixed-tensor augmentation lemmas prove the rank
identity in both cases, including both cuts adjacent to the middle letter.
-/

namespace CriticalGK2.Actual

noncomputable section

open CriticalGK2.ContractionBudget

variable (F : Type*) [Field F]

/-- Literal actual cut rank of the coefficient tensor of a polynomial. -/
def polynomialCutRank (a b : ℕ) (P : WordAlgebra F) : ℕ :=
  wordCutRank F a b (ambientToDual F (a + b) P)

theorem homogeneousDualDegreeCast_symm_eq {a b : ℕ} (h : a = b) :
    homogeneousDualDegreeCast F h.symm = (homogeneousDualDegreeCast F h).symm := by
  subst b
  rfl

theorem polynomialCutRank_append (a b c : ℕ) (P Q : WordAlgebra F)
    (hP : P ∈ homogeneous F (a + b)) (hQ : Q ∈ homogeneous F c) (hQ0 : Q ≠ 0) :
    polynomialCutRank F a (b + c) (P * Q) = polynomialCutRank F a b P := by
  unfold polynomialCutRank
  rw [← ambientToDual_degreeCast F (Nat.add_assoc a b c) (P * Q),
    ambientToDual_mul F (a + b) c P Q hP hQ]
  exact wordCutRank_append F a b c (ambientToDual F (a + b) P)
    (ambientToDual F c Q) (ambientToDual_ne_zero F c Q hQ hQ0)

theorem polynomialCutRank_prepend (c a b : ℕ) (P Q : WordAlgebra F)
    (hP : P ∈ homogeneous F c) (hP0 : P ≠ 0) (hQ : Q ∈ homogeneous F (a + b)) :
    polynomialCutRank F (c + a) b (P * Q) = polynomialCutRank F a b Q := by
  unfold polynomialCutRank
  rw [← ambientToDual_degreeCast F (Nat.add_assoc c a b).symm (P * Q),
    ambientToDual_mul F c (a + b) P Q hP hQ, homogeneousDualDegreeCast_symm_eq]
  exact wordCutRank_prepend F c a b (ambientToDual F c P)
    (ambientToDual_ne_zero F c P hP hP0) (ambientToDual F (a + b) Q)

/-- All literal cuts of one homogeneous polynomial have bounded actual rank. -/
def PolynomialCutBound (q : ℕ) (P : WordAlgebra F) (B : ℕ) : Prop :=
  ∀ a b : ℕ, a + b = q → polynomialCutRank F a b P ≤ B

/-- The actual finite maximum over all physical cuts, including both
scalar endpoint cuts. -/
def polynomialCutBudget (q : ℕ) (P : WordAlgebra F) : ℕ :=
  (Finset.range (q + 1)).sup fun a => polynomialCutRank F a (q - a) P

theorem polynomialCutBudget_le_iff (q : ℕ) (P : WordAlgebra F) (B : ℕ) :
    polynomialCutBudget F q P ≤ B ↔ PolynomialCutBound F q P B := by
  unfold polynomialCutBudget
  rw [Finset.sup_le_iff]
  constructor
  · intro h a b hab
    have ha : a ∈ Finset.range (q + 1) := Finset.mem_range.mpr (by omega)
    have hb : q - a = b := by omega
    simpa only [hb] using h a ha
  · intro h a ha
    have hal : a ≤ q := by have := Finset.mem_range.mp ha; omega
    exact h a (q - a) (by omega)

/-- Actual one-letter homogeneous membership. -/
theorem binaryLetter_mem_homogeneous (b : Bool) : binaryLetter F b ∈ homogeneous F 1 := by
  apply (wordHomogeneous_iff_mem_homogeneous F 1 _).mp
  simpa only [binaryLetter, FreeMonoid.length_of] using
    (wordHomogeneous_single (FreeMonoid.of b) (1 : F))

/-- Every cut in the waiting polynomial has exactly the rank of a cut
in one of its two actual copies of P. -/
theorem polynomialCutBound_waiting (q : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F q) (hP0 : P ≠ 0) (B : ℕ)
    (hB : PolynomialCutBound F q P B) :
    PolynomialCutBound F (2 * q + 1) ((P * binaryLetter F false) * P) B := by
  intro a b hab
  by_cases ha : a ≤ q
  · obtain ⟨c, hq⟩ := Nat.exists_eq_add_of_le ha
    have hb : b = c + (1 + q) := by omega
    subst b
    have hPc : P ∈ homogeneous F (a + c) := by simpa only [hq] using hP
    have hQP : binaryLetter F false * P ∈ homogeneous F (1 + q) :=
      homogeneous_mul F (binaryLetter_mem_homogeneous F false) hP
    have hQP0 : binaryLetter F false * P ≠ 0 :=
      mul_ne_zero (binaryLetter_ne_zero F false) hP0
    have hr := polynomialCutRank_append F a c (1 + q) P (binaryLetter F false * P)
      hPc hQP hQP0
    rw [mul_assoc, hr]
    exact hB a c hq.symm
  · have hqa : q + 1 ≤ a := by omega
    obtain ⟨c, ha⟩ := Nat.exists_eq_add_of_le hqa
    have hcb : c + b = q := by omega
    have hQP : P * binaryLetter F false ∈ homogeneous F (q + 1) :=
      homogeneous_mul F hP (binaryLetter_mem_homogeneous F false)
    have hQP0 : P * binaryLetter F false ≠ 0 :=
      mul_ne_zero hP0 (binaryLetter_ne_zero F false)
    have hPc : P ∈ homogeneous F (c + b) := by simpa only [hcb] using hP
    rw [ha, polynomialCutRank_prepend F (q + 1) c b
      (P * binaryLetter F false) P hQP hQP0 hPc]
    exact hB c b hcb

/-- Every old physical cut occurs in the first copy of P, so the converse
bound holds without losing information. -/
theorem polynomialCutBound_of_waiting (q : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F q) (hP0 : P ≠ 0) (B : ℕ)
    (hB : PolynomialCutBound F (2 * q + 1) ((P * binaryLetter F false) * P) B) :
    PolynomialCutBound F q P B := by
  intro a b hab
  have hPc : P ∈ homogeneous F (a + b) := by simpa only [hab] using hP
  have hQP : binaryLetter F false * P ∈ homogeneous F (1 + q) :=
    homogeneous_mul F (binaryLetter_mem_homogeneous F false) hP
  have hQP0 : binaryLetter F false * P ≠ 0 :=
    mul_ne_zero (binaryLetter_ne_zero F false) hP0
  have hr := polynomialCutRank_append F a b (1 + q) P (binaryLetter F false * P)
    hPc hQP hQP0
  have hb := hB a (b + (1 + q)) (by omega)
  rw [mul_assoc, hr] at hb
  exact hb

/-- Waiting preserves the intrinsic budget, by preserving every cut rank. -/
theorem polynomialCutBudget_waiting (q : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F q) (hP0 : P ≠ 0) :
    polynomialCutBudget F (2 * q + 1) ((P * binaryLetter F false) * P) =
      polynomialCutBudget F q P := by
  apply Nat.le_antisymm
  · apply (polynomialCutBudget_le_iff F _ _ _).mpr
    apply polynomialCutBound_waiting F q P hP hP0
    exact (polynomialCutBudget_le_iff F q P _).mp le_rfl
  · apply (polynomialCutBudget_le_iff F _ _ _).mpr
    apply polynomialCutBound_of_waiting F q P hP hP0
    exact (polynomialCutBudget_le_iff F _ _ _).mp le_rfl

/-- The concrete waiting step already used by the infinite construction
has this actual computed invariant. -/
theorem waitingStem_polynomialCutBudget (n : ℕ) (t : StemWord n → F) (ht : t ≠ 0) :
    polynomialCutBudget F (2 * n + 1) (waitingStem F n t) =
      polynomialCutBudget F n (stemPolynomial F n t) := by
  exact polynomialCutBudget_waiting F n (stemPolynomial F n t)
    ((wordHomogeneous_iff_mem_homogeneous F n _).mp (stemPolynomial_homogeneous F n t))
    (stemPolynomial_ne_zero F n t ht)

#print axioms CriticalGK2.Actual.polynomialCutBudget_waiting

end

end CriticalGK2.Actual
