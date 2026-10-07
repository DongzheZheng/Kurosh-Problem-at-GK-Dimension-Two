import CriticalGK2.AllCutClosure
import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# The actual all-cut submodule is an actual two-sided ideal

The degree-one closure theorems from `AllCutClosure` extend to arbitrary
word products by free monoid induction and to arbitrary algebra elements
by finite linear expansion. The quotient is the `RingCon.Quotient` of the
free algebra.

Survival in this ring quotient follows from the nontriviality of
`ComponentQuotient = H_n / E_n` and the exact intersection
`allCutSubmodule ∩ homogeneous n = allCutComponent n`. Equivalently, the
comaps along `homogeneous n .subtype` agree. This intersection identity is
proved in `HomogeneousProjection.lean`.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

theorem allCutSubmodule_mul_degreeOne (W : DyadicDualData F)
    (hW : PrimalCoherent F W) {x y : WordAlgebra F}
    (hx : x ∈ allCutSubmodule F W) (hy : y ∈ homogeneous F 1) :
    x * y ∈ allCutSubmodule F W := by
  have hle : allCutSubmodule F W ≤
      (allCutSubmodule F W).comap (rightMultiplication F y) := by
    apply iSup_le
    intro n z hz
    have hzy := allCutComponent_mul_letter F W hW (n + 1)
      (mul_mem_productSpan F hz hy)
    exact (le_iSup (fun m => allCutComponent F W (m + 1)) (n + 1)) hzy
  exact hle hx

theorem degreeOne_mul_allCutSubmodule (W : DyadicDualData F)
    (hW : PrimalCoherent F W) {x y : WordAlgebra F}
    (hx : x ∈ homogeneous F 1) (hy : y ∈ allCutSubmodule F W) :
    x * y ∈ allCutSubmodule F W := by
  have hle : allCutSubmodule F W ≤
      (allCutSubmodule F W).comap (leftMultiplication F x) := by
    apply iSup_le
    intro n z hz
    have hxz := letter_mul_allCutComponent F W hW (n + 1)
      (mul_mem_productSpan F hx hz)
    exact (le_iSup (fun m => allCutComponent F W (m + 1)) (n + 1)) hxz
  exact hle hy

theorem monomialOne_mul_allCutSubmodule (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (w : Word) :
    ∀ x : WordAlgebra F, x ∈ allCutSubmodule F W →
      MonoidAlgebra.single w 1 * x ∈ allCutSubmodule F W := by
  refine FreeMonoid.recOn w ?_ ?_
  ·
      intro x hx
      simpa only [← MonoidAlgebra.one_def, one_mul] using hx
  ·
      intro b w ih x hx
      have hletter : MonoidAlgebra.single (FreeMonoid.of b) (1 : F) ∈ homogeneous F 1 :=
        monomial_mem_homogeneous F 1 ⟨FreeMonoid.of b, FreeMonoid.length_of b⟩ 1
      have h := degreeOne_mul_allCutSubmodule F W hW hletter (ih x hx)
      simpa only [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul] using h

theorem allCutSubmodule_mul_monomialOne (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (w : Word) :
    ∀ x : WordAlgebra F, x ∈ allCutSubmodule F W →
      x * MonoidAlgebra.single w 1 ∈ allCutSubmodule F W := by
  refine FreeMonoid.recOn w ?_ ?_
  ·
      intro x hx
      simpa only [← MonoidAlgebra.one_def, mul_one] using hx
  ·
      intro b w ih x hx
      have hletter : MonoidAlgebra.single (FreeMonoid.of b) (1 : F) ∈ homogeneous F 1 :=
        monomial_mem_homogeneous F 1 ⟨FreeMonoid.of b, FreeMonoid.length_of b⟩ 1
      have hstep := allCutSubmodule_mul_degreeOne F W hW hx hletter
      have h := ih (x * MonoidAlgebra.single (FreeMonoid.of b) 1) hstep
      simpa only [mul_assoc, MonoidAlgebra.single_mul_single, one_mul] using h

theorem allCutSubmodule_mul_mem_left (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (a x : WordAlgebra F)
    (hx : x ∈ allCutSubmodule F W) : a * x ∈ allCutSubmodule F W := by
  classical
  induction a using Finsupp.induction with
  | zero =>
      change (0 : WordAlgebra F) * x ∈ allCutSubmodule F W
      rw [zero_mul]
      exact (allCutSubmodule F W).zero_mem
  | single_add w c a hwa hc ih =>
      change (MonoidAlgebra.single w c + MonoidAlgebra.ofCoeff a) * x ∈ allCutSubmodule F W
      rw [add_mul]
      apply (allCutSubmodule F W).add_mem _ ih
      have hsingle : MonoidAlgebra.single w c = c • MonoidAlgebra.single w (1 : F) := by
        simp [MonoidAlgebra.single, Finsupp.smul_single]
      rw [hsingle, smul_mul_assoc]
      exact (allCutSubmodule F W).smul_mem c
        (monomialOne_mul_allCutSubmodule F W hW w x hx)

theorem allCutSubmodule_mul_mem_right (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (x a : WordAlgebra F)
    (hx : x ∈ allCutSubmodule F W) : x * a ∈ allCutSubmodule F W := by
  classical
  induction a using Finsupp.induction with
  | zero =>
      change x * (0 : WordAlgebra F) ∈ allCutSubmodule F W
      rw [mul_zero]
      exact (allCutSubmodule F W).zero_mem
  | single_add w c a hwa hc ih =>
      change x * (MonoidAlgebra.single w c + MonoidAlgebra.ofCoeff a) ∈ allCutSubmodule F W
      rw [mul_add]
      apply (allCutSubmodule F W).add_mem _ ih
      have hsingle : MonoidAlgebra.single w c = c • MonoidAlgebra.single w (1 : F) := by
        simp [MonoidAlgebra.single, Finsupp.smul_single]
      rw [hsingle, mul_smul_comm]
      exact (allCutSubmodule F W).smul_mem c
        (allCutSubmodule_mul_monomialOne F W hW w x hx)

/-- An actual two-sided ideal, whose closure obligations have just been proved. -/
def allCutTwoSidedIdeal (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    TwoSidedIdeal (WordAlgebra F) :=
  TwoSidedIdeal.mk' (allCutSubmodule F W : Set (WordAlgebra F))
    (allCutSubmodule F W).zero_mem
    (fun hx hy => (allCutSubmodule F W).add_mem hx hy)
    (fun hx => (allCutSubmodule F W).neg_mem hx)
    (fun {x y} hy => allCutSubmodule_mul_mem_left F W hW x y hy)
    (fun {x y} hx => allCutSubmodule_mul_mem_right F W hW x y hx)

@[simp]
theorem mem_allCutTwoSidedIdeal (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (x : WordAlgebra F) :
    x ∈ allCutTwoSidedIdeal F W hW ↔ x ∈ allCutSubmodule F W := by
  simp [allCutTwoSidedIdeal]

/-- The ring quotient by the all-cut two-sided ideal. -/
abbrev AllCutRingQuotient (W : DyadicDualData F) (hW : PrimalCoherent F W) :=
  (allCutTwoSidedIdeal F W hW).ringCon.Quotient

end

end CriticalGK2.Actual
