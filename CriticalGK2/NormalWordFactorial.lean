import CriticalGK2.PositiveQuotient

/-!
# Actual normal words and factor closure in the actual quotient

The order is the literal binary code of actual finite Bool words. Its fixed-
length injectivity and concatenation compatibility are proved. A normal word
is defined by nonmembership of its actual singleton quotient image in the
span of earlier word images.

The actual quotient map is the original all-cut ring quotient map. Its
multiplicativity proves that nonnormal factors make every enclosing word
nonnormal. The basis, counting and infinite-path lemmas build on this
factor closure.
-/

namespace CriticalGK2.WordOrder

noncomputable section

/-- Literal big-endian binary code, with False less than True. -/
def binaryCode : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 1 else 0) * 2 ^ w.length + binaryCode w

/-- Exact compatibility of the actual code with actual word concatenation. -/
theorem binaryCode_append (u v : List Bool) :
    binaryCode (u ++ v) = binaryCode u * 2 ^ v.length + binaryCode v := by
  induction u with
  | nil => simp [binaryCode]
  | cons b u ih =>
      simp only [List.cons_append, binaryCode, List.length_append, pow_add, ih]
      ring

theorem binaryCode_lt_two_pow (w : List Bool) : binaryCode w < 2 ^ w.length := by
  induction w with
  | nil => simp [binaryCode]
  | cons b w ih =>
      cases b <;> simp only [binaryCode, List.length_cons, pow_succ] <;> simp at * <;> omega

/-- At any fixed length, the actual binary code is injective. -/
theorem binaryCode_injective_of_length_eq {u v : List Bool}
    (hlen : u.length = v.length) (hcode : binaryCode u = binaryCode v) : u = v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => rfl
      | cons b v => simp at hlen
  | cons b u ih =>
      cases v with
      | nil => simp at hlen
      | cons d v =>
          have htail : u.length = v.length := Nat.succ.inj hlen
          have hu := binaryCode_lt_two_pow u
          have hv := binaryCode_lt_two_pow v
          rw [htail] at hu
          have hbit : b = d := by
            cases b <;> cases d <;> try rfl
            all_goals simp [binaryCode, htail] at hcode <;> omega
          subst d
          have hc : binaryCode u = binaryCode v := by
            cases b <;> simp [binaryCode, htail] at hcode <;> omega
          congr 1
          apply ih <;> assumption

/-- The code of the literal actual free-monoid word. -/
def wordNumber (w : CriticalGK2.Actual.Word) : ℕ := binaryCode w.toList

theorem wordNumber_mul (u v : CriticalGK2.Actual.Word) :
    wordNumber (u * v) = wordNumber u * 2 ^ v.length + wordNumber v := by
  simpa only [wordNumber, FreeMonoid.toList_mul, FreeMonoid.length] using
    binaryCode_append u.toList v.toList

/-- Fixed-length substitution preserves the literal actual strict word order. -/
theorem wordNumber_sandwich_lt (a b u v : CriticalGK2.Actual.Word)
    (hlen : v.length = u.length) (hcode : wordNumber v < wordNumber u) :
    wordNumber (a * v * b) < wordNumber (a * u * b) := by
  have hp : 0 < (2 : ℕ) ^ b.length := pow_pos (by omega) _
  have hm := Nat.mul_lt_mul_of_pos_right hcode hp
  simp only [wordNumber_mul, add_mul]
  rw [hlen]
  omega

theorem lengthWordNumber_injective (n : ℕ) :
    Function.Injective (fun w : CriticalGK2.Actual.LengthWord n => wordNumber w.val) := by
  intro u v hcode
  apply Subtype.ext
  have hlen : u.val.toList.length = v.val.toList.length := by
    simpa only [FreeMonoid.length] using u.property.trans v.property.symm
  have hlist := binaryCode_injective_of_length_eq hlen hcode
  simpa only [FreeMonoid.ofList_toList] using congrArg FreeMonoid.ofList hlist

/-- A literal finite linear order on the actual homogeneous word indexing type. -/
@[reducible]
def lengthWordLinearOrder (n : ℕ) : LinearOrder (CriticalGK2.Actual.LengthWord n) :=
  LinearOrder.lift' (fun w => wordNumber w.val) (lengthWordNumber_injective n)

end

end CriticalGK2.WordOrder

namespace CriticalGK2.Actual

open CriticalGK2.WordOrder

noncomputable section

variable (F : Type*) [Field F]

/-- Actual coefficient-one singleton word evaluated in the original actual quotient. -/
def quotientWord (W : DyadicDualData F) (hW : PrimalCoherent F W) (w : Word) :
    AllCutRingQuotient F W hW :=
  allCutQuotientMap F W hW (MonoidAlgebra.single w (1 : F))

theorem quotientWord_mul (W : DyadicDualData F) (hW : PrimalCoherent F W) (u v : Word) :
    quotientWord F W hW (u * v) = quotientWord F W hW u * quotientWord F W hW v := by
  unfold quotientWord
  rw [← map_mul]
  congr 1
  simp only [MonoidAlgebra.single_mul_single, one_mul]

/-- All actual quotient images of strictly earlier actual same-degree words. -/
def earlierWordImages (W : DyadicDualData F) (hW : PrimalCoherent F W) (w : Word) :
    Set (AllCutRingQuotient F W hW) :=
  {z | ∃ v : Word, v.length = w.length ∧ wordNumber v < wordNumber w ∧
    quotientWord F W hW v = z}

/-- Normal words are closed under taking contiguous factors. -/
def NormalWord (W : DyadicDualData F) (hW : PrimalCoherent F W) (w : Word) : Prop :=
  quotientWord F W hW w ∉ Submodule.span F (earlierWordImages F W hW w)

/-- Multiplication by the actual left and right singleton quotient images. -/
def quotientWordSandwich (W : DyadicDualData F) (hW : PrimalCoherent F W) (a b : Word) :
    AllCutRingQuotient F W hW →ₗ[F] AllCutRingQuotient F W hW where
  toFun z := quotientWord F W hW a * z * quotientWord F W hW b
  map_add' x y := by rw [mul_add, add_mul]
  map_smul' c x := by
    rw [mul_smul_comm, smul_mul_assoc]
    simp only [RingHom.id_apply]

@[simp]
theorem quotientWordSandwich_word (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (a b v : Word) :
    quotientWordSandwich F W hW a b (quotientWord F W hW v) =
      quotientWord F W hW (a * v * b) := by
  change quotientWord F W hW a * quotientWord F W hW v * quotientWord F W hW b = _
  rw [quotientWord_mul, quotientWord_mul]

/-- Earlier-word span substitution is an actual linear-map consequence of
actual quotient multiplication and the proved actual word-order compatibility. -/
theorem earlierWordSpan_sandwich (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (a b u : Word) :
    Submodule.span F (earlierWordImages F W hW u) ≤
      (Submodule.span F (earlierWordImages F W hW (a * u * b))).comap
        (quotientWordSandwich F W hW a b) := by
  apply Submodule.span_le.mpr
  intro z hz
  obtain ⟨v, hlen, hcode, rfl⟩ := hz
  change quotientWordSandwich F W hW a b (quotientWord F W hW v) ∈
    Submodule.span F (earlierWordImages F W hW (a * u * b))
  rw [quotientWordSandwich_word]
  apply Submodule.subset_span
  refine ⟨a * v * b, ?_, wordNumber_sandwich_lt a b u v hlen hcode, rfl⟩
  simp only [FreeMonoid.length_mul, hlen]

/-- Every contiguous factor of a normal word is normal, by the two-sided
quotient relation. -/
theorem NormalWord_factor (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (a u b : Word) (hnormal : NormalWord F W hW (a * u * b)) : NormalWord F W hW u := by
  classical
  by_contra hu
  have hmem : quotientWord F W hW u ∈ Submodule.span F (earlierWordImages F W hW u) := by
    simpa only [NormalWord, not_not] using hu
  have hm := earlierWordSpan_sandwich F W hW a b u hmem
  change quotientWordSandwich F W hW a b (quotientWord F W hW u) ∈
    Submodule.span F (earlierWordImages F W hW (a * u * b)) at hm
  rw [quotientWordSandwich_word] at hm
  exact hnormal hm

/-- A zero actual word quotient image automatically makes that word nonnormal. -/
theorem not_NormalWord_of_quotientWord_eq_zero (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (u : Word) (hu : quotientWord F W hW u = 0) :
    ¬ NormalWord F W hW u := by
  intro hnormal
  apply hnormal
  rw [hu]
  exact Submodule.zero_mem _

#print axioms CriticalGK2.WordOrder.lengthWordNumber_injective
#print axioms CriticalGK2.Actual.earlierWordSpan_sandwich
#print axioms CriticalGK2.Actual.NormalWord_factor

end

end CriticalGK2.Actual
