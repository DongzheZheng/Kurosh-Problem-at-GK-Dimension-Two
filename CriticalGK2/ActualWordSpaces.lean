import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# Actual word-algebra semantics for the sparse dual construction

The ambient ring is the actual monoid algebra `F[FreeMonoid Bool]`.
Homogeneous components are actual supported submodules, with their actual
word bases, multiplication and dual spaces. The definitions specify the
spaces `W`, their annihilators `U`, and the all-cut components.

The component quotients are vector-space quotients. Closure under left and
right multiplication, established in `AllCutClosure` and `AllCutIdeal`, gives
the ring quotient.
-/

namespace CriticalGK2.Actual

noncomputable section

abbrev Word := FreeMonoid Bool

abbrev WordAlgebra (F : Type*) [Semiring F] := MonoidAlgebra F Word

def wordsOfLength (n : ℕ) : Set Word := {w | w.length = n}

abbrev LengthWord (n : ℕ) := {w : Word // w.length = n}

/-- An actual length-n word is equivalently a vector of n Boolean letters. -/
def lengthWordEquivVector (n : ℕ) : LengthWord n ≃ List.Vector Bool n where
  toFun w := ⟨w.val.toList, w.property⟩
  invFun w := ⟨FreeMonoid.ofList w.val, w.property⟩
  left_inv w := by apply Subtype.ext; rfl
  right_inv w := by apply Subtype.ext; rfl

noncomputable instance lengthWordFintype (n : ℕ) : Fintype (LengthWord n) :=
  Fintype.ofEquiv (List.Vector Bool n) (lengthWordEquivVector n).symm

theorem card_lengthWord (n : ℕ) : Fintype.card (LengthWord n) = 2 ^ n := by
  rw [Fintype.card_congr (lengthWordEquivVector n)]
  simp

/-- Concatenation of actual words, keeping the lengths in the type. -/
def concatenate {a b : ℕ} (u : LengthWord a) (v : LengthWord b) : LengthWord (a + b) :=
  ⟨u.val * v.val, by simp [FreeMonoid.length_mul, u.property, v.property]⟩

@[simp]
theorem concatenate_val {a b : ℕ} (u : LengthWord a) (v : LengthWord b) :
    (concatenate u v).val = u.val * v.val := rfl

/-- The left part of an actual word at the specified cut. -/
def cutLeft (a b : ℕ) (w : LengthWord (a + b)) : LengthWord a :=
  ⟨FreeMonoid.ofList (w.val.toList.take a), by
    change (w.val.toList.take a).length = a
    have hwlen : w.val.toList.length = a + b := w.property
    rw [List.length_take, hwlen]
    exact Nat.min_eq_left (Nat.le_add_right a b)⟩

/-- The right part of an actual word at the specified cut. -/
def cutRight (a b : ℕ) (w : LengthWord (a + b)) : LengthWord b :=
  ⟨FreeMonoid.ofList (w.val.toList.drop a), by
    change (w.val.toList.drop a).length = b
    have hwlen : w.val.toList.length = a + b := w.property
    rw [List.length_drop, hwlen, Nat.add_sub_cancel_left]⟩

theorem concatenate_cut (a b : ℕ) (w : LengthWord (a + b)) :
    concatenate (cutLeft a b w) (cutRight a b w) = w := by
  apply Subtype.ext
  change FreeMonoid.ofList
    (w.val.toList.take a ++ w.val.toList.drop a) = w.val
  rw [List.take_append_drop, FreeMonoid.ofList_toList]

@[simp]
theorem cutLeft_concatenate {a b : ℕ} (u : LengthWord a) (v : LengthWord b) :
    cutLeft a b (concatenate u v) = u := by
  apply Subtype.ext
  change FreeMonoid.ofList ((u.val.toList ++ v.val.toList).take a) = u.val
  rw [List.take_left' u.property, FreeMonoid.ofList_toList]

@[simp]
theorem cutRight_concatenate {a b : ℕ} (u : LengthWord a) (v : LengthWord b) :
    cutRight a b (concatenate u v) = v := by
  apply Subtype.ext
  change FreeMonoid.ofList ((u.val.toList ++ v.val.toList).drop a) = v.val
  rw [List.drop_left' u.property, FreeMonoid.ofList_toList]

/-- Every actual word has a unique left/right decomposition at a fixed cut. -/
def concatenateEquiv (a b : ℕ) : LengthWord a × LengthWord b ≃ LengthWord (a + b) where
  toFun p := concatenate p.1 p.2
  invFun w := (cutLeft a b w, cutRight a b w)
  left_inv p := by simp
  right_inv := concatenate_cut a b

@[simp]
theorem concatenateEquiv_apply (a b : ℕ) (p : LengthWord a × LengthWord b) :
    concatenateEquiv a b p = concatenate p.1 p.2 := rfl

@[simp]
theorem concatenateEquiv_symm_apply (a b : ℕ) (w : LengthWord (a + b)) :
    (concatenateEquiv a b).symm w = (cutLeft a b w, cutRight a b w) := rfl

section Field

variable (F : Type*) [Field F]

/-- Actual degree-n submodule of the two-letter free algebra. -/
def homogeneous (n : ℕ) : Submodule F (WordAlgebra F) :=
  Finsupp.supported F F (wordsOfLength n)

theorem mem_homogeneous_iff (n : ℕ) (x : WordAlgebra F) :
    x ∈ homogeneous F n ↔ ∀ w : Word, w.length ≠ n → x w = 0 := by
  exact Finsupp.mem_supported' F x

theorem monomial_mem_homogeneous (n : ℕ) (w : LengthWord n) (c : F) :
    MonoidAlgebra.single w.val c ∈ homogeneous F n :=
  Finsupp.single_mem_supported F c w.property

/-- Restriction of coefficients is the actual homogeneous word-basis equivalence. -/
noncomputable def homogeneousWordEquiv (n : ℕ) :
    homogeneous F n ≃ₗ[F] (LengthWord n →₀ F) :=
  Finsupp.supportedEquivFinsupp (wordsOfLength n)

theorem finrank_homogeneous (n : ℕ) :
    Module.finrank F (homogeneous F n) = 2 ^ n := by
  rw [(homogeneousWordEquiv F n).finrank_eq]
  rw [Module.finrank_finsupp_self, card_lengthWord]

theorem finrank_homogeneous_zero : Module.finrank F (homogeneous F 0) = 1 := by
  rw [finrank_homogeneous]
  simp

/-- Actual multiplication respects actual word length. -/
theorem homogeneous_mul {a b : ℕ} {x y : WordAlgebra F}
    (hx : x ∈ homogeneous F a) (hy : y ∈ homogeneous F b) :
    x * y ∈ homogeneous F (a + b) := by
  classical
  change ∀ w ∈ (x * y).support, w ∈ wordsOfLength (a + b)
  intro w hw
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp (MonoidAlgebra.support_mul x y hw)
  have hu' : u.length = a := hx hu
  have hv' : v.length = b := hy hv
  simpa [wordsOfLength, FreeMonoid.length_mul, hu', hv']

/-- The scalar character that sends the two actual generators to zero. -/
def constantCharacter : Word →* F where
  toFun w := if w.length = 0 then 1 else 0
  map_one' := by simp
  map_mul' u v := by
    by_cases hu : u.length = 0 <;> by_cases hv : v.length = 0 <;>
      simp [FreeMonoid.length_mul, Nat.add_eq_zero, hu, hv]

/-- The actual augmentation of the free algebra: both letters map to zero. -/
noncomputable def augmentation : WordAlgebra F →ₐ[F] F :=
  MonoidAlgebra.lift F F Word (constantCharacter F)

@[simp]
theorem augmentation_monomial (w : Word) (c : F) :
    augmentation F (MonoidAlgebra.single w c) =
      c * (if w.length = 0 then 1 else 0) := by
  simp [augmentation, MonoidAlgebra.lift_single, constantCharacter, smul_eq_mul]

@[simp]
theorem augmentation_letter (b : Bool) :
    augmentation F (MonoidAlgebra.single (FreeMonoid.of b) 1) = 0 := by
  simp

/-- The positive part is a proved, actual two-sided ideal of the free algebra. -/
noncomputable def augmentationIdeal : TwoSidedIdeal (WordAlgebra F) :=
  TwoSidedIdeal.ker (augmentation F)

/-- Actual degree-n dual vector space. -/
abbrev HomogeneousDual (n : ℕ) := Module.Dual F (homogeneous F n)

/-- A family of dual subspaces indexed by dyadic degrees. -/
abbrev DyadicDualData := (h : ℕ) → Submodule F (HomogeneousDual F (2 ^ h))

/-- Original-space annihilator of the actual dyadic dual space. -/
def dyadicAnnihilator (W : DyadicDualData F) (h : ℕ) :
    Submodule F (homogeneous F (2 ^ h)) := (W h).dualCoannihilator

theorem mem_dyadicAnnihilator_iff (W : DyadicDualData F) (h : ℕ)
    (x : homogeneous F (2 ^ h)) :
    x ∈ dyadicAnnihilator F W h ↔ ∀ φ ∈ W h, φ x = 0 :=
  Submodule.mem_dualCoannihilator x

/-- The same annihilator included into the actual ambient word algebra. -/
def ambientAnnihilator (W : DyadicDualData F) (h : ℕ) :
    Submodule F (WordAlgebra F) :=
  (dyadicAnnihilator F W h).map (homogeneous F (2 ^ h)).subtype

def rightMultiplication (b : WordAlgebra F) : WordAlgebra F →ₗ[F] WordAlgebra F where
  toFun a := a * b
  map_add' a a' := add_mul a a' b
  map_smul' c a := smul_mul_assoc c a b

def leftMultiplication (a : WordAlgebra F) : WordAlgebra F →ₗ[F] WordAlgebra F where
  toFun b := a * b
  map_add' b b' := mul_add a b b'
  map_smul' c b := mul_smul_comm c a b

def strictDyadicRoot (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- Raw right completion space in the actual word algebra, with its endpoint. -/
def rightCompletion (W : DyadicDualData F) (n : ℕ) : Submodule F (WordAlgebra F) :=
  if n = 0 then ⊥ else
    homogeneous F n ⊓
      ⨅ b : homogeneous F (2 ^ strictDyadicRoot n - n),
        (ambientAnnihilator F W (strictDyadicRoot n)).comap
          (rightMultiplication F b.val)

/-- Raw left completion space in the actual word algebra, with its endpoint. -/
def leftCompletion (W : DyadicDualData F) (n : ℕ) : Submodule F (WordAlgebra F) :=
  if n = 0 then ⊥ else
    homogeneous F n ⊓
      ⨅ a : homogeneous F (2 ^ strictDyadicRoot n - n),
        (ambientAnnihilator F W (strictDyadicRoot n)).comap
          (leftMultiplication F a.val)

@[simp]
theorem rightCompletion_zero (W : DyadicDualData F) : rightCompletion F W 0 = ⊥ := by
  simp [rightCompletion]

@[simp]
theorem leftCompletion_zero (W : DyadicDualData F) : leftCompletion F W 0 = ⊥ := by
  simp [leftCompletion]

/-- The actual linear span of products of elements of two submodules. -/
def productSpan (S T : Submodule F (WordAlgebra F)) : Submodule F (WordAlgebra F) :=
  Submodule.span F {z | ∃ x ∈ S, ∃ y ∈ T, x * y = z}

theorem mul_mem_productSpan {S T : Submodule F (WordAlgebra F)}
    {x y : WordAlgebra F} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ productSpan F S T :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

theorem productSpan_le_iff (S T P : Submodule F (WordAlgebra F)) :
    productSpan F S T ≤ P ↔
      ∀ x ∈ S, ∀ y ∈ T, x * y ∈ P := by
  constructor
  · intro h x hx y hy
    exact h (mul_mem_productSpan F hx hy)
  · intro h
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    exact h x hx y hy

theorem productSpan_mono {S S' T T' : Submodule F (WordAlgebra F)}
    (hS : S ≤ S') (hT : T ≤ T') : productSpan F S T ≤ productSpan F S' T' := by
  rw [productSpan_le_iff]
  intro x hx y hy
  exact mul_mem_productSpan F (hS hx) (hT hy)

/-- Associativity is proved for actual spans of actual algebra products. -/
theorem productSpan_assoc (S T U : Submodule F (WordAlgebra F)) :
    productSpan F (productSpan F S T) U = productSpan F S (productSpan F T U) := by
  apply le_antisymm
  · rw [productSpan_le_iff]
    intro x hx z hz
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨u, hu, v, hv, rfl⟩ := hx
        rw [mul_assoc]
        exact mul_mem_productSpan F hu (mul_mem_productSpan F hv hz)
    | zero => simpa using (productSpan F S (productSpan F T U)).zero_mem
    | add x y hx hy ihx ihy =>
        simpa only [add_mul] using (productSpan F S (productSpan F T U)).add_mem ihx ihy
    | smul c x hx ih =>
        simpa only [smul_mul_assoc] using
          (productSpan F S (productSpan F T U)).smul_mem c ih
  · rw [productSpan_le_iff]
    intro x hx z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨u, hu, v, hv, rfl⟩ := hz
        rw [← mul_assoc]
        exact mul_mem_productSpan F (mul_mem_productSpan F hx hu) hv
    | zero => simpa using (productSpan F (productSpan F S T) U).zero_mem
    | add z z' hz hz' ihz ihz' =>
        simpa only [mul_add] using (productSpan F (productSpan F S T) U).add_mem ihz ihz'
    | smul c z hz ih =>
        simpa only [mul_smul_comm] using
          (productSpan F (productSpan F S T) U).smul_mem c ih

/-- Every actual homogeneous word splits at a fixed cut, so products span the
whole next homogeneous component, not merely a contained subspace. -/
theorem homogeneous_productSpan (a b : ℕ) :
    productSpan F (homogeneous F a) (homogeneous F b) = homogeneous F (a + b) := by
  apply le_antisymm
  · rw [productSpan_le_iff]
    intro x hx y hy
    exact homogeneous_mul F hx hy
  · change Finsupp.supported F F (wordsOfLength (a + b)) ≤ _
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro z ⟨w, hw, rfl⟩
    let w' : LengthWord (a + b) := ⟨w, hw⟩
    let u := cutLeft a b w'
    let v := cutRight a b w'
    have hword : u.val * v.val = w :=
      congrArg Subtype.val (concatenate_cut a b w')
    have hproduct :
        MonoidAlgebra.single u.val (1 : F) * MonoidAlgebra.single v.val 1 =
          MonoidAlgebra.single w 1 := by
      simp [MonoidAlgebra.single_mul_single, hword]
    change MonoidAlgebra.single w (1 : F) ∈ _
    rw [← hproduct]
    exact mul_mem_productSpan F (monomial_mem_homogeneous F a u 1)
      (monomial_mem_homogeneous F b v 1)

theorem homogeneous_zero_eq_span_one :
    homogeneous F 0 = Submodule.span F {(1 : WordAlgebra F)} := by
  have hwords : wordsOfLength 0 = {(1 : Word)} := by
    ext w
    simp [wordsOfLength, FreeMonoid.length_eq_zero]
  change Finsupp.supported F F (wordsOfLength 0) = _
  rw [hwords, Finsupp.supported_eq_span_single]
  rw [Set.image_singleton]
  rfl

theorem productSpan_bot_left (T : Submodule F (WordAlgebra F)) :
    productSpan F ⊥ T = ⊥ := by
  apply eq_bot_iff.mpr
  rw [productSpan_le_iff]
  intro x hx y hy
  have hx0 : x = 0 := (Submodule.mem_bot F).mp hx
  simp [hx0]

theorem productSpan_bot_right (S : Submodule F (WordAlgebra F)) :
    productSpan F S ⊥ = ⊥ := by
  apply eq_bot_iff.mpr
  rw [productSpan_le_iff]
  intro x hx y hy
  have hy0 : y = 0 := (Submodule.mem_bot F).mp hy
  simp [hy0]

theorem productSpan_homogeneous_zero_left (S : Submodule F (WordAlgebra F)) :
    productSpan F (homogeneous F 0) S = S := by
  rw [homogeneous_zero_eq_span_one]
  apply le_antisymm
  · rw [productSpan_le_iff]
    intro x hx y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simpa only [smul_mul_assoc, one_mul] using S.smul_mem c hy
  · intro x hx
    have h1 : (1 : WordAlgebra F) ∈ Submodule.span F {(1 : WordAlgebra F)} :=
      Submodule.subset_span (by simp)
    simpa using mul_mem_productSpan F h1 hx

theorem productSpan_homogeneous_zero_right (S : Submodule F (WordAlgebra F)) :
    productSpan F S (homogeneous F 0) = S := by
  rw [homogeneous_zero_eq_span_one]
  apply le_antisymm
  · rw [productSpan_le_iff]
    intro x hx y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simpa only [mul_smul_comm, mul_one] using S.smul_mem c hx
  · intro x hx
    have h1 : (1 : WordAlgebra F) ∈ Submodule.span F {(1 : WordAlgebra F)} :=
      Submodule.subset_span (by simp)
    simpa using mul_mem_productSpan F hx h1

/-- The exact all-cut intersection in homogeneous degree n. -/
def allCutComponent (W : DyadicDualData F) (n : ℕ) :
    Submodule F (WordAlgebra F) :=
  homogeneous F n ⊓
    ⨅ i : Fin (n + 1),
      productSpan F (leftCompletion F W i.val) (homogeneous F (n - i.val)) ⊔
      productSpan F (homogeneous F i.val) (rightCompletion F W (n - i.val))

theorem allCutComponent_le_homogeneous (W : DyadicDualData F) (n : ℕ) :
    allCutComponent F W n ≤ homogeneous F n := inf_le_left

/-- The actual first endpoint of the all-cut intersection gives R(n). -/
theorem allCutComponent_le_rightCompletion (W : DyadicDualData F) (n : ℕ) :
    allCutComponent F W n ≤ rightCompletion F W n := by
  intro x hx
  have hi := (Submodule.mem_iInf _).mp hx.2 (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  simpa only [Nat.sub_zero, Fin.val_zero, leftCompletion_zero,
    productSpan_bot_left, productSpan_homogeneous_zero_left, bot_sup_eq] using hi

/-- The actual last endpoint of the all-cut intersection gives L(n). -/
theorem allCutComponent_le_leftCompletion (W : DyadicDualData F) (n : ℕ) :
    allCutComponent F W n ≤ leftCompletion F W n := by
  intro x hx
  have hi := (Submodule.mem_iInf _).mp hx.2 (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
  simpa only [Nat.sub_self, rightCompletion_zero,
    productSpan_bot_right, productSpan_homogeneous_zero_right, sup_bot_eq] using hi

/-- The genuine homogeneous vector-space quotient.  Ring quotient structure
awaits the actual left and right ideal-closure proof. -/
abbrev ComponentQuotient (W : DyadicDualData F) (n : ℕ) :=
  homogeneous F n ⧸ (allCutComponent F W n).comap (homogeneous F n).subtype

/-- The direct sum of the all-cut components, represented as a submodule. -/
def allCutSubmodule (W : DyadicDualData F) : Submodule F (WordAlgebra F) :=
  ⨆ n : ℕ, allCutComponent F W (n + 1)

end Field

end

end CriticalGK2.Actual
