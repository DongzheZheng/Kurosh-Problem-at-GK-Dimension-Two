import CriticalGK2.SameFieldReadback
import CriticalGK2.PositiveQuotient
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Actual finite-dimensional tail quotients separate the positive algebra

The tail ideal is defined by the original word coefficients. Its two-sided
closure follows from actual free-word multiplication. Adding it to the actual
all-cut ideal gives literal ring quotients. Each quotient is the image of the
finite-dimensional subspace of words shorter than the cutoff. A nonzero
actual quotient element has a surviving homogeneous component, and that
component survives the corresponding tail quotient.

The separation theorem applies to every coherent all-cut family.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- Literal words shorter than the cutoff. -/
abbrev ShortWord (N : ℕ) := {w : Word // w.length < N}

instance shortWordFinite (N : ℕ) : Finite (ShortWord N) := by
  let f : ShortWord N → Σ n : Fin N, LengthWord n.val :=
    fun w => ⟨⟨w.val.length, w.property⟩, ⟨w.val, rfl⟩⟩
  apply Finite.of_injective f
  intro w v h
  apply Subtype.ext
  exact congrArg (fun p : Σ n : Fin N, LengthWord n.val => p.2.val) h

/-- The actual finite-dimensional span of short words. -/
def shortWordSubmodule (N : ℕ) : Submodule F (WordAlgebra F) :=
  Finsupp.supported F F {w : Word | w.length < N}

instance shortWordSubmodule_finite (N : ℕ) :
    FiniteDimensional F (shortWordSubmodule F N) := by
  let e : shortWordSubmodule F N ≃ₗ[F] (ShortWord N →₀ F) :=
    Finsupp.supportedEquivFinsupp {w : Word | w.length < N}
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- The literal degree-at-least-N subspace in the free algebra. -/
def wordTailSubmodule (N : ℕ) : Submodule F (WordAlgebra F) :=
  Finsupp.supported F F {w : Word | N ≤ w.length}

@[simp]
theorem mem_wordTailSubmodule (N : ℕ) (P : WordAlgebra F) :
    P ∈ wordTailSubmodule F N ↔ ∀ w : Word, w.length < N → P w = 0 := by
  change P ∈ Finsupp.supported F F {w : Word | N ≤ w.length} ↔ _
  simpa only [Set.mem_setOf_eq, not_le] using (Finsupp.mem_supported' (s := {w : Word | N ≤ w.length}) F P)

theorem wordTailSubmodule_mul_left (N : ℕ) (P Q : WordAlgebra F)
    (hQ : Q ∈ wordTailSubmodule F N) : P * Q ∈ wordTailSubmodule F N := by
  classical
  change ∀ w ∈ (P * Q).support, N ≤ w.length
  intro w hw
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp (MonoidAlgebra.support_mul P Q hw)
  have hvN : N ≤ v.length := hQ hv
  simpa only [FreeMonoid.length_mul] using hvN.trans (Nat.le_add_left v.length u.length)

theorem wordTailSubmodule_mul_right (N : ℕ) (P Q : WordAlgebra F)
    (hP : P ∈ wordTailSubmodule F N) : P * Q ∈ wordTailSubmodule F N := by
  classical
  change ∀ w ∈ (P * Q).support, N ≤ w.length
  intro w hw
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp (MonoidAlgebra.support_mul P Q hw)
  have huN : N ≤ u.length := hP hu
  simpa only [FreeMonoid.length_mul] using huN.trans (Nat.le_add_right u.length v.length)

/-- Genuine two-sided tail ideal of the original free word algebra. -/
def wordTailIdeal (N : ℕ) : TwoSidedIdeal (WordAlgebra F) :=
  TwoSidedIdeal.mk' (wordTailSubmodule F N : Set (WordAlgebra F))
    (wordTailSubmodule F N).zero_mem
    (fun hx hy => (wordTailSubmodule F N).add_mem hx hy)
    (fun hx => (wordTailSubmodule F N).neg_mem hx)
    (fun {P Q} hQ => wordTailSubmodule_mul_left F N P Q hQ)
    (fun {P Q} hP => wordTailSubmodule_mul_right F N P Q hP)

@[simp]
theorem mem_wordTailIdeal (N : ℕ) (P : WordAlgebra F) :
    P ∈ wordTailIdeal F N ↔ P ∈ wordTailSubmodule F N := by simp [wordTailIdeal]

/-- Actual coefficient truncation, with codomain the short-word submodule. -/
def shortWordProjection (N : ℕ) : WordAlgebra F →ₗ[F] shortWordSubmodule F N := by
  classical
  exact Finsupp.restrictDom F F {w : Word | w.length < N}

@[simp]
theorem shortWordProjection_coeff (N : ℕ) (P : WordAlgebra F) (w : Word) :
    (shortWordProjection F N P).val w = if w.length < N then P w else 0 := by
  classical
  change (Finsupp.filter (fun w : Word => w.length < N) (MonoidAlgebra.coeff P)) w = _
  rw [Finsupp.filter_apply]
  rfl

theorem sub_shortWordProjection_mem_tail (N : ℕ) (P : WordAlgebra F) :
    P - (shortWordProjection F N P).val ∈ wordTailSubmodule F N := by
  rw [mem_wordTailSubmodule]
  intro w hw
  change P w - (shortWordProjection F N P).val w = 0
  rw [shortWordProjection_coeff, if_pos hw, sub_self]

theorem homogeneousProjection_tail_eq_zero (N n : ℕ) (hn : n < N)
    (P : WordAlgebra F) (hP : P ∈ wordTailSubmodule F N) :
    homogeneousProjection F n P = 0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro w
  rw [homogeneousProjection_coeff]
  by_cases hw : w.length = n
  · rw [if_pos hw]
    exact (mem_wordTailSubmodule F N P).mp hP w (by omega)
  · rw [if_neg hw]
    rfl

/-- The actual finite truncation relation E plus the original word tail. -/
def finiteTruncationIdeal (W : DyadicDualData F) (hW : PrimalCoherent F W) (N : ℕ) :
    TwoSidedIdeal (WordAlgebra F) := allCutTwoSidedIdeal F W hW ⊔ wordTailIdeal F N

/-- A literal ring quotient of the original free algebra. -/
abbrev FiniteTruncation (W : DyadicDualData F) (hW : PrimalCoherent F W) (N : ℕ) :=
  (finiteTruncationIdeal F W hW N).ringCon.Quotient

def finiteTruncationQuotientMap (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (N : ℕ) : WordAlgebra F →ₐ[F] FiniteTruncation F W hW N :=
  (finiteTruncationIdeal F W hW N).ringCon.mkₐ F

@[simp]
theorem finiteTruncationQuotientMap_eq_zero_iff (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) (P : WordAlgebra F) :
    finiteTruncationQuotientMap F W hW N P = 0 ↔ P ∈ finiteTruncationIdeal F W hW N := by
  change (finiteTruncationIdeal F W hW N).ringCon.mk' P = 0 ↔ _
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

/-- Every actual truncated quotient element has an actual short representative. -/
theorem finiteTruncation_short_surjective (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    Function.Surjective ((finiteTruncationQuotientMap F W hW N).toLinearMap.comp
      (shortWordSubmodule F N).subtype) := by
  intro x
  obtain ⟨P, rfl⟩ := RingCon.mkₐ_surjective (S := F) (finiteTruncationIdeal F W hW N).ringCon x
  refine ⟨shortWordProjection F N P, ?_⟩
  change finiteTruncationQuotientMap F W hW N (shortWordProjection F N P).val =
    finiteTruncationQuotientMap F W hW N P
  apply Eq.symm
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (finiteTruncationQuotientMap_eq_zero_iff F W hW N _).mpr
  exact TwoSidedIdeal.mem_sup_right ((mem_wordTailIdeal F N _).mpr
    (sub_shortWordProjection_mem_tail F N P))

/-- Actual finite dimensionality follows from the actual finite word span. -/
instance finiteTruncation_finite (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) : FiniteDimensional F (FiniteTruncation F W hW N) :=
  FiniteDimensional.of_surjective
    ((finiteTruncationQuotientMap F W hW N).toLinearMap.comp (shortWordSubmodule F N).subtype)
    (finiteTruncation_short_surjective F W hW N)

/-- Actual factor map H/E -> H/(E+tail), as an algebra homomorphism. -/
def finiteTruncationFactor (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (N : ℕ) : AllCutRingQuotient F W hW →ₐ[F] FiniteTruncation F W hW N :=
  RingCon.factorₐ F (TwoSidedIdeal.ringCon_le_iff.mp (show
    allCutTwoSidedIdeal F W hW ≤ finiteTruncationIdeal F W hW N from le_sup_left))

@[simp]
theorem finiteTruncationFactor_map (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) (P : WordAlgebra F) :
    finiteTruncationFactor F W hW N (allCutQuotientMap F W hW P) =
      finiteTruncationQuotientMap F W hW N P := rfl

/-- Restriction of the actual factor map to the actual positive algebra. -/
def positiveFiniteTruncationMap (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (N : ℕ) : PositiveAllCutQuotient F W hW →ₙₐ[F] FiniteTruncation F W hW N where
  toFun a := finiteTruncationFactor F W hW N a.val
  map_zero' := (finiteTruncationFactor F W hW N).map_zero
  map_add' a b := (finiteTruncationFactor F W hW N).map_add a.val b.val
  map_mul' a b := (finiteTruncationFactor F W hW N).map_mul a.val b.val
  map_smul' c a := (finiteTruncationFactor F W hW N).toLinearMap.map_smul c a.val

/-- Every actual nonzero element survives a literal finite-dimensional tail quotient. -/
theorem exists_positive_finiteTruncation_separating (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (a : PositiveAllCutQuotient F W hW) (ha : a ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ positiveFiniteTruncationMap F W hW N a ≠ 0 := by
  classical
  obtain ⟨P, hP⟩ := allCutQuotientMap_surjective F W hW a.val
  have hPnot : P ∉ allCutSubmodule F W := by
    intro h
    apply ha
    apply Subtype.ext
    exact hP.symm.trans ((allCutQuotientMap_eq_zero_iff F W hW P).mpr h)
  have hex : ∃ n : ℕ, (homogeneousProjection F n P).val ∉ allCutComponent F W n := by
    by_contra h
    push_neg at h
    exact hPnot (mem_allCutSubmodule_of_homogeneousProjections_mem F W P h)
  obtain ⟨n, hn⟩ := hex
  refine ⟨n + 1, by omega, ?_⟩
  intro hzero
  have hz : finiteTruncationQuotientMap F W hW (n + 1) P = 0 := by
    rw [← finiteTruncationFactor_map, hP]
    exact hzero
  have hmem := (finiteTruncationQuotientMap_eq_zero_iff F W hW (n + 1) P).mp hz
  obtain ⟨Epart, hE, Tpart, hT, hsum⟩ := TwoSidedIdeal.mem_sup.mp hmem
  have hTzero : homogeneousProjection F n Tpart = 0 :=
    homogeneousProjection_tail_eq_zero F (n + 1) n (by omega) Tpart
      ((mem_wordTailIdeal F (n + 1) Tpart).mp hT)
  have hprojection : homogeneousProjection F n P = homogeneousProjection F n Epart := by
    rw [← hsum, map_add, hTzero, add_zero]
  apply hn
  rw [hprojection]
  exact homogeneousProjection_allCutSubmodule_mem F W n Epart
    ((mem_allCutTwoSidedIdeal F W hW Epart).mp hE)

/-- The literal image of the positive quotient in the tail quotient.  The
carrier is defined directly so its scalar structure is the actual `F`-module
structure, independently of generic hom-class elaboration. -/
def positiveFiniteTruncationSubalgebra (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    NonUnitalSubalgebra F (FiniteTruncation F W hW N) where
  carrier := {x | ∃ a, positiveFiniteTruncationMap F W hW N a = x}
  zero_mem' := ⟨0, (positiveFiniteTruncationMap F W hW N).map_zero'⟩
  add_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (positiveFiniteTruncationMap F W hW N).map_add' a b⟩
  mul_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, (positiveFiniteTruncationMap F W hW N).map_mul' a b⟩
  smul_mem' := by
    rintro c x ⟨a, rfl⟩
    exact ⟨c • a, (positiveFiniteTruncationMap F W hW N).map_smul' c a⟩

/-- The actual image is the finite-dimensional non-unital quotient target. -/
def PositiveFiniteTruncationImage (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) : Type _ :=
  ↥(positiveFiniteTruncationSubalgebra F W hW N)

instance positiveFiniteTruncationImageNonUnitalRing (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    NonUnitalRing (PositiveFiniteTruncationImage F W hW N) :=
  NonUnitalSubalgebra.toNonUnitalRing (positiveFiniteTruncationSubalgebra F W hW N)

instance positiveFiniteTruncationImageModule (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    Module F (PositiveFiniteTruncationImage F W hW N) :=
  NonUnitalSubalgebra.instModule (S := positiveFiniteTruncationSubalgebra F W hW N)

instance positiveFiniteTruncationImageScalarTower (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    IsScalarTower F (PositiveFiniteTruncationImage F W hW N)
      (PositiveFiniteTruncationImage F W hW N) where
  smul_assoc c x y := Subtype.ext (smul_mul_assoc c x.val y.val)

instance positiveFiniteTruncationImageSMulComm (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    SMulCommClass F (PositiveFiniteTruncationImage F W hW N)
      (PositiveFiniteTruncationImage F W hW N) where
  smul_comm c x y := Subtype.ext (mul_smul_comm c x.val y.val).symm

instance positiveFiniteTruncationImage_finite (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    FiniteDimensional F (PositiveFiniteTruncationImage F W hW N) := by
  exact inferInstanceAs (FiniteDimensional F
    (positiveFiniteTruncationSubalgebra F W hW N).toSubmodule)

def positiveFiniteTruncationSurjection (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    PositiveAllCutQuotient F W hW →ₙₐ[F] PositiveFiniteTruncationImage F W hW N where
  toFun a := ⟨positiveFiniteTruncationMap F W hW N a, a, rfl⟩
  map_zero' := Subtype.ext (positiveFiniteTruncationMap F W hW N).map_zero'
  map_add' a b := Subtype.ext ((positiveFiniteTruncationMap F W hW N).map_add' a b)
  map_mul' a b := Subtype.ext ((positiveFiniteTruncationMap F W hW N).map_mul' a b)
  map_smul' c a := Subtype.ext ((positiveFiniteTruncationMap F W hW N).map_smul' c a)

theorem positiveFiniteTruncationSurjection_surjective (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    Function.Surjective (positiveFiniteTruncationSurjection F W hW N) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, rfl⟩

/-- Residual finite dimensionality as actual surjective non-unital algebra
maps to the explicitly finite-dimensional image quotients. -/
theorem positive_residually_finite_dimensional (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (a : PositiveAllCutQuotient F W hW) (ha : a ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ positiveFiniteTruncationSurjection F W hW N a ≠ 0 := by
  obtain ⟨N, hN, hsep⟩ := exists_positive_finiteTruncation_separating F W hW a ha
  refine ⟨N, hN, ?_⟩
  intro hz
  exact hsep (congrArg Subtype.val hz)

#print axioms CriticalGK2.Actual.wordTailSubmodule_mul_left
#print axioms CriticalGK2.Actual.finiteTruncation_finite
#print axioms CriticalGK2.Actual.positive_residually_finite_dimensional

end

end CriticalGK2.Actual
