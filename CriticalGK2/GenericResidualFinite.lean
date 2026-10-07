import CriticalGK2.HomogeneousIdealZorn

/-!
# Residual finite dimensionality for arbitrary actual homogeneous ideals

The original word-tail spaces and their two-sided closure come from
ActualResidualFinite. Here the ideal is any literal two-sided ideal closed
under the actual coefficient projections. The targets are literal quotients
H/(I+tail_N), proved finite dimensional from actual short-word representatives.
Homogeneity separates each nonzero element in one of these tail quotients.
-/

namespace CriticalGK2.GenericResidual

noncomputable section

open CriticalGK2.Actual
open scoped BigOperators

variable (F : Type*) [Field F]

abbrev WordRingQuotient (I : TwoSidedIdeal (WordAlgebra F)) := I.ringCon.Quotient

def quotientMap (I : TwoSidedIdeal (WordAlgebra F)) :
    WordAlgebra F →ₐ[F] WordRingQuotient F I := I.ringCon.mkₐ F

@[simp]
theorem quotientMap_eq_zero_iff (I : TwoSidedIdeal (WordAlgebra F)) (P : WordAlgebra F) :
    quotientMap F I P = 0 ↔ P ∈ I := by
  change I.ringCon.mk' P = 0 ↔ P ∈ I
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

def truncationIdeal (I : TwoSidedIdeal (WordAlgebra F)) (N : ℕ) :
    TwoSidedIdeal (WordAlgebra F) := I ⊔ wordTailIdeal F N

abbrev Truncation (I : TwoSidedIdeal (WordAlgebra F)) (N : ℕ) :=
  WordRingQuotient F (truncationIdeal F I N)

def truncationMap (I : TwoSidedIdeal (WordAlgebra F)) (N : ℕ) :
    WordAlgebra F →ₐ[F] Truncation F I N := quotientMap F (truncationIdeal F I N)

/-- Actual short representatives cover the entire literal truncation quotient. -/
theorem short_surjective (I : TwoSidedIdeal (WordAlgebra F)) (N : ℕ) :
    Function.Surjective ((truncationMap F I N).toLinearMap.comp (shortWordSubmodule F N).subtype) := by
  intro x
  obtain ⟨P, rfl⟩ := RingCon.mkₐ_surjective (S := F) (truncationIdeal F I N).ringCon x
  refine ⟨shortWordProjection F N P, ?_⟩
  change truncationMap F I N (shortWordProjection F N P).val = truncationMap F I N P
  apply Eq.symm
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (quotientMap_eq_zero_iff F (truncationIdeal F I N) _).mpr
  exact TwoSidedIdeal.mem_sup_right ((mem_wordTailIdeal F N _).mpr
    (sub_shortWordProjection_mem_tail F N P))

instance truncation_finite (I : TwoSidedIdeal (WordAlgebra F)) (N : ℕ) :
    FiniteDimensional F (Truncation F I N) :=
  FiniteDimensional.of_surjective
    ((truncationMap F I N).toLinearMap.comp (shortWordSubmodule F N).subtype)
    (short_surjective F I N)

/-- Actual quotient factorization, with its proved ideal inclusion. -/
def factor (I : TwoSidedIdeal (WordAlgebra F)) (N : ℕ) :
    WordRingQuotient F I →ₐ[F] Truncation F I N :=
  RingCon.factorₐ F (TwoSidedIdeal.ringCon_le_iff.mp
    (show I ≤ truncationIdeal F I N from le_sup_left))

@[simp]
theorem factor_map (I : TwoSidedIdeal (WordAlgebra F)) (N : ℕ) (P : WordAlgebra F) :
    factor F I N (quotientMap F I P) = truncationMap F I N P := rfl

/-- Finite coefficient reconstruction is valid for every actual F-linear ideal. -/
theorem mem_ideal_of_projections_mem (I : TwoSidedIdeal (WordAlgebra F))
    (P : WordAlgebra F) (hP : ∀ n : ℕ, (homogeneousProjection F n P).val ∈ I) : P ∈ I := by
  change P ∈ wordIdealSubmodule F I
  rw [← sum_homogeneousProjection_eq F P]
  exact (wordIdealSubmodule F I).sum_mem (fun n _ => hP n)

/-- Every nonzero element of an actual homogeneous quotient survives an
actual finite-dimensional tail quotient. -/
theorem quotient_residually_finite_dimensional
    (I : TwoSidedIdeal (WordAlgebra F)) (hI : WordIdealHomogeneous F I)
    (a : WordRingQuotient F I) (ha : a ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ factor F I N a ≠ 0 := by
  classical
  obtain ⟨P, hP⟩ := RingCon.mkₐ_surjective (S := F) I.ringCon a
  change quotientMap F I P = a at hP
  have hPnot : P ∉ I := by
    intro h
    apply ha
    exact hP.symm.trans ((quotientMap_eq_zero_iff F I P).mpr h)
  have hex : ∃ n : ℕ, (homogeneousProjection F n P).val ∉ I := by
    by_contra h
    push_neg at h
    exact hPnot (mem_ideal_of_projections_mem F I P h)
  obtain ⟨n, hn⟩ := hex
  refine ⟨n + 1, by omega, ?_⟩
  intro hzero
  have hz : truncationMap F I (n + 1) P = 0 := by rw [← factor_map, hP]; exact hzero
  have hmem := (quotientMap_eq_zero_iff F (truncationIdeal F I (n + 1)) P).mp hz
  obtain ⟨Epart, hE, Tpart, hT, hsum⟩ := TwoSidedIdeal.mem_sup.mp hmem
  have hTzero : homogeneousProjection F n Tpart = 0 :=
    homogeneousProjection_tail_eq_zero F (n + 1) n (by omega) Tpart
      ((mem_wordTailIdeal F (n + 1) Tpart).mp hT)
  have hprojection : homogeneousProjection F n P = homogeneousProjection F n Epart := by
    rw [← hsum, map_add, hTzero, add_zero]
  apply hn
  rw [hprojection]
  exact hI n Epart hE

/-- Any actual included non-unital subalgebra inherits these separating
maps into the proved finite-dimensional targets. -/
theorem included_algebra_residually_finite_dimensional
    (I : TwoSidedIdeal (WordAlgebra F)) (hI : WordIdealHomogeneous F I)
    {A : Type*} [NonUnitalRing A] [Module F A] [IsScalarTower F A A] [SMulCommClass F A A]
    (j : A →ₙₐ[F] WordRingQuotient F I) (hj : Function.Injective j) (a : A) (ha : a ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ((factor F I N).toNonUnitalAlgHom.comp j) a ≠ 0 := by
  have hja : j a ≠ 0 := by intro h; exact ha (hj (h.trans j.map_zero.symm))
  obtain ⟨N, hN, hsep⟩ := quotient_residually_finite_dimensional F I hI (j a) hja
  exact ⟨N, hN, hsep⟩

#print axioms CriticalGK2.GenericResidual.truncation_finite
#print axioms CriticalGK2.GenericResidual.quotient_residually_finite_dimensional
#print axioms CriticalGK2.GenericResidual.included_algebra_residually_finite_dimensional

end

end CriticalGK2.GenericResidual
