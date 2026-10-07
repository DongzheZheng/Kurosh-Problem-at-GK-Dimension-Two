import CriticalGK2.PositiveGrowthFiltration
import CriticalGK2.PositiveGeneration
import CriticalGK2.NormalLanguagePath

/-!
# The actual degree filtration is the two-letter word-growth filtration

The bounded word index consists of literal nonempty words in the original
two-letter free monoid. Its image in A uses the actual positive quotient map.
The degree filtration is identified with the F-linear span of these actual
word images, using actual homogeneous monomials in one direction and the
actual homogeneous word basis in the other.

The images preserve actual word multiplication and agree with the two actual
generators at one-letter words. Thus the finite dimensions used in the growth
proof refer to the standard filtration by positive words in those generators.
-/

namespace CriticalGK2.Actual

noncomputable section

open scoped BigOperators

variable (F : Type*) [Field F]

/-- A nonempty left word makes its literal concatenation nonempty. -/
theorem word_mul_ne_one_of_left (u v : Word) (hu : u ≠ 1) : u * v ≠ 1 := by
  intro he
  have hlen := congrArg FreeMonoid.length he
  have huLen : u.length ≠ 0 := fun h => hu (FreeMonoid.length_eq_zero.mp h)
  rw [FreeMonoid.length_mul] at hlen
  change u.length + v.length = 0 at hlen
  apply huLen
  omega

/-- Actual positive word images preserve literal word concatenation. -/
theorem positiveWordImage_mul (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (u v : Word) (hu : u ≠ 1) (hv : v ≠ 1) :
    positiveWordImage F W hW (u * v) (word_mul_ne_one_of_left u v hu) =
      positiveWordImage F W hW u hu * positiveWordImage F W hW v hv := by
  apply Subtype.ext
  change quotientWord F W hW (u * v) = quotientWord F W hW u * quotientWord F W hW v
  exact quotientWord_mul F W hW u v

/-- The literal one-letter image is precisely the specified actual generator. -/
theorem positiveWordImage_letter (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (b : Bool) (hb : (FreeMonoid.of b : Word) ≠ 1) :
    positiveWordImage F W hW (FreeMonoid.of b) hb = positiveGenerator F W hW b := by
  apply Subtype.ext
  rfl

/-- The actual nonempty words of length at most the cutoff. -/
def BoundedPositiveWord (N : ℕ) := {w : Word // 0 < w.length ∧ w.length ≤ N}

theorem boundedPositiveWord_ne_one (N : ℕ) (w : BoundedPositiveWord N) : w.val ≠ 1 := by
  intro h
  have hlen := w.property.1
  rw [h] at hlen
  exact Nat.not_lt_zero _ hlen

/-- The actual quotient image of a bounded literal word. -/
def boundedPositiveWordImage (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (N : ℕ) (w : BoundedPositiveWord N) : PositiveAllCutQuotient F W hW :=
  positiveWordImage F W hW w.val (boundedPositiveWord_ne_one N w)

/-- The standard word-growth filtration for the two actual letter images. -/
def positiveWordFiltration (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (N : ℕ) : Submodule F (PositiveAllCutQuotient F W hW) :=
  Submodule.span F (Set.range (boundedPositiveWordImage F W hW N))

/-- A literal word image lies in the actual degree filtration at its cutoff. -/
theorem boundedPositiveWordImage_mem_degreeFiltration (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) (w : BoundedPositiveWord N) :
    boundedPositiveWordImage F W hW N w ∈ positiveDegreeFiltration F W hW N := by
  have hwpos := w.property.1
  have hwbound := w.property.2
  let m : ℕ := w.val.length - 1
  have hdegree : w.val.length = m + 1 := by dsimp [m]; omega
  have hm : m < N := by dsimp [m]; omega
  let x : homogeneous F (m + 1) :=
    ⟨MonoidAlgebra.single w.val 1, monomial_mem_homogeneous F (m + 1)
      ⟨w.val, hdegree⟩ 1⟩
  have hx := homogeneousToPositiveQuotient_mem_filtration F W hW m N hm x
  have heq : homogeneousToPositiveQuotient F W hW (m + 1) (by omega) x =
      boundedPositiveWordImage F W hW N w := by
    apply Subtype.ext
    rfl
  rw [heq] at hx
  exact hx

/-- Every generator of the word span lies in the actual finite degree sum. -/
theorem positiveWordFiltration_le_degreeFiltration (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    positiveWordFiltration F W hW N ≤ positiveDegreeFiltration F W hW N := by
  apply Submodule.span_le.mpr
  rintro a ⟨w, rfl⟩
  exact boundedPositiveWordImage_mem_degreeFiltration F W hW N w

/-- The actual homogeneous word-basis expansion puts every finite positive
degree image in the span of the bounded actual word images. -/
theorem positiveDegreeFiltration_le_wordFiltration (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    positiveDegreeFiltration F W hW N ≤ positiveWordFiltration F W hW N := by
  classical
  unfold positiveDegreeFiltration
  apply Finset.sup_le
  intro m hm
  rintro a ⟨q, rfl⟩
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective
    ((allCutComponent F W (m + 1)).comap (homogeneous F (m + 1)).subtype) q
  rw [← hx, componentQuotientToPositive_mk,
    ← (homogeneousWordBasis F (m + 1)).sum_repr x, map_sum]
  apply Submodule.sum_mem
  intro w _
  rw [map_smul]
  apply Submodule.smul_mem
  let wb : BoundedPositiveWord N :=
    ⟨w.val, by rw [w.property]; omega, by
      rw [w.property]
      have hm' := Finset.mem_range.mp hm
      omega⟩
  have heq : homogeneousToPositiveQuotient F W hW (m + 1) (by omega)
      (homogeneousWordBasis F (m + 1) w) = boundedPositiveWordImage F W hW N wb := by
    apply Subtype.ext
    change allCutQuotientMap F W hW (homogeneousWordBasis F (m + 1) w).val =
      allCutQuotientMap F W hW (MonoidAlgebra.single w.val 1)
    rw [homogeneousWordBasis_coe]
  rw [heq]
  exact Submodule.subset_span ⟨wb, rfl⟩

/-- Exact identity with the standard actual two-letter word span. -/
theorem positiveDegreeFiltration_eq_wordFiltration (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    positiveDegreeFiltration F W hW N = positiveWordFiltration F W hW N :=
  le_antisymm (positiveDegreeFiltration_le_wordFiltration F W hW N)
    (positiveWordFiltration_le_degreeFiltration F W hW N)

/-- The actual growth dimension is the standard bounded word-span dimension. -/
theorem positiveDegreeGrowth_eq_wordSpan_finrank (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (N : ℕ) :
    positiveDegreeGrowth F W hW N =
      Module.finrank F (Submodule.span F (Set.range (boundedPositiveWordImage F W hW N))) := by
  unfold positiveDegreeGrowth
  rw [positiveDegreeFiltration_eq_wordFiltration]
  rfl

#print axioms CriticalGK2.Actual.positiveWordImage_mul
#print axioms CriticalGK2.Actual.positiveWordImage_letter
#print axioms CriticalGK2.Actual.positiveDegreeFiltration_eq_wordFiltration
#print axioms CriticalGK2.Actual.positiveDegreeGrowth_eq_wordSpan_finrank

end

end CriticalGK2.Actual
