import CriticalGK2.PositiveWordIdealWordProducts
import CriticalGK2.PositiveWordIdealScalarNil
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The actual unitization of the positive further quotient

The literal augmentation split identifies Unitization F Q with the actual
unital word quotient H/I. Its actual cutoff is the image of F times the
positive cutoff, has dimension exactly one plus its positive counterpart,
and agrees with the span of the empty word and the bounded nonempty words.
-/

namespace CriticalGK2.Actual

noncomputable section

open Filter
open scoped Topology

variable (F : Type*) [Field F]
variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)

/-- The actual extension of the augmentation-kernel inclusion. -/
def positiveUnitizationToWordQuotient :
    Unitization F (PositiveWordIdealQuotient F I hpos) →ₐ[F] WordIdealQuotient F I :=
  (positiveWordIdealInclusion F I hpos).toAlgHom

@[simp]
theorem positiveUnitizationToWordQuotient_apply
    (x : Unitization F (PositiveWordIdealQuotient F I hpos)) :
    positiveUnitizationToWordQuotient F I hpos x =
      algebraMap F (WordIdealQuotient F I) x.fst + x.snd.val := rfl

theorem positiveUnitizationToWordQuotient_injective :
    Function.Injective (positiveUnitizationToWordQuotient F I hpos) := by
  intro x y h
  change algebraMap F (WordIdealQuotient F I) x.fst + x.snd.val =
    algebraMap F (WordIdealQuotient F I) y.fst + y.snd.val at h
  have hfst := congrArg (wordIdealQuotientAugmentation F I hpos) h
  have hx : wordIdealQuotientAugmentation F I hpos x.snd.val = 0 := x.snd.property
  have hy : wordIdealQuotientAugmentation F I hpos y.snd.val = 0 := y.snd.property
  simp only [map_add, AlgHom.commutes, hx, hy, add_zero] at hfst
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hfst
  have hsnd : x.snd.val = y.snd.val := by
    rw [hfst] at h
    exact add_left_cancel h
  exact Unitization.ext hfst (Subtype.ext hsnd)

theorem positiveUnitizationToWordQuotient_surjective :
    Function.Surjective (positiveUnitizationToWordQuotient F I hpos) := by
  intro b
  obtain ⟨c, a, hb⟩ := positiveWordIdeal_scalar_split F I hpos b
  refine ⟨Unitization.mk (c, a), ?_⟩
  change algebraMap F (WordIdealQuotient F I) c + a.val = b
  rw [Algebra.algebraMap_eq_smul_one]
  exact hb.symm

/-- A genuine algebra equivalence between the same actual unitization and
its literal unital word quotient. -/
def positiveUnitizationWordQuotientEquiv :
    Unitization F (PositiveWordIdealQuotient F I hpos) ≃ₐ[F] WordIdealQuotient F I :=
  AlgEquiv.ofBijective (positiveUnitizationToWordQuotient F I hpos)
    ⟨positiveUnitizationToWordQuotient_injective F I hpos,
      positiveUnitizationToWordQuotient_surjective F I hpos⟩

theorem positiveUnitization_not_finite
    (hinfinite : ¬ Module.Finite F (PositiveWordIdealQuotient F I hpos)) :
    ¬ Module.Finite F (Unitization F (PositiveWordIdealQuotient F I hpos)) := by
  intro hfinite
  letI : Module.Finite F (Unitization F (PositiveWordIdealQuotient F I hpos)) := hfinite
  exact hinfinite (FiniteDimensional.of_injective
    (Unitization.inrHom F (PositiveWordIdealQuotient F I hpos)) Unitization.inr_injective)

/-- An actual scalar-plus-cutoff linear embedding into the actual unitization. -/
def positiveUnitizationCutoffMap (N : ℕ) :
    F × positiveIdealDegreeFiltration F I hpos N →ₗ[F]
      Unitization F (PositiveWordIdealQuotient F I hpos) where
  toFun p := Unitization.mk (p.1, p.2.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem positiveUnitizationCutoffMap_injective (N : ℕ) :
    Function.Injective (positiveUnitizationCutoffMap F I hpos N) := by
  intro x y h
  change Unitization.mk (x.1, x.2.val) = Unitization.mk (y.1, y.2.val) at h
  have hprod := congrArg Unitization.toProd h
  change (x.1, x.2.val) = (y.1, y.2.val) at hprod
  have hfst : x.1 = y.1 :=
    congrArg (fun z : F × PositiveWordIdealQuotient F I hpos => z.1) hprod
  have hsnd : x.2.val = y.2.val :=
    congrArg (fun z : F × PositiveWordIdealQuotient F I hpos => z.2) hprod
  exact Prod.ext hfst (Subtype.ext hsnd)

/-- The actual unital cutoff, including its empty word. -/
def positiveUnitizationDegreeFiltration (N : ℕ) :
    Submodule F (Unitization F (PositiveWordIdealQuotient F I hpos)) :=
  LinearMap.range (positiveUnitizationCutoffMap F I hpos N)

instance positiveUnitizationDegreeFiltration_finite (N : ℕ) :
    FiniteDimensional F (positiveUnitizationDegreeFiltration F I hpos N) := by
  apply FiniteDimensional.of_surjective
    (positiveUnitizationCutoffMap F I hpos N).rangeRestrict
  intro z
  obtain ⟨p, hp⟩ := z.property
  exact ⟨p, Subtype.ext hp⟩

def positiveUnitizationDegreeGrowth (N : ℕ) : ℕ :=
  Module.finrank F (positiveUnitizationDegreeFiltration F I hpos N)

/-- Exact dimension addition; this is an equality of actual cutoff dimensions. -/
theorem positiveUnitizationDegreeGrowth_eq (N : ℕ) :
    positiveUnitizationDegreeGrowth F I hpos N = 1 + positiveIdealDegreeGrowth F I hpos N := by
  unfold positiveUnitizationDegreeGrowth positiveUnitizationDegreeFiltration
  rw [LinearMap.finrank_range_of_inj (positiveUnitizationCutoffMap_injective F I hpos N)]
  rw [Module.finrank_prod, CommSemiring.finrank_self]
  rfl

@[simp]
theorem mem_positiveUnitizationDegreeFiltration (N : ℕ)
    (x : Unitization F (PositiveWordIdealQuotient F I hpos)) :
    x ∈ positiveUnitizationDegreeFiltration F I hpos N ↔
      x.snd ∈ positiveIdealDegreeFiltration F I hpos N := by
  constructor
  · rintro ⟨⟨c, a⟩, rfl⟩
    exact a.property
  · intro hx
    exact ⟨(x.fst, ⟨x.snd, hx⟩), Unitization.ext rfl rfl⟩

theorem positiveUnitizationDegreeFiltration_eq_scalar_sup (N : ℕ) :
    positiveUnitizationDegreeFiltration F I hpos N =
      Submodule.span F {(1 : Unitization F (PositiveWordIdealQuotient F I hpos))} ⊔
        (positiveIdealDegreeFiltration F I hpos N).map
          (Unitization.inrHom F (PositiveWordIdealQuotient F I hpos)) := by
  apply le_antisymm
  · intro x hx
    have hxs := (mem_positiveUnitizationDegreeFiltration F I hpos N x).mp hx
    refine Submodule.mem_sup.mpr ⟨x.fst • 1, ?_, (x.snd : Unitization F _), ?_, ?_⟩
    · exact Submodule.smul_mem _ x.fst (Submodule.subset_span (Set.mem_singleton 1))
    · exact ⟨x.snd, hxs, rfl⟩
    · apply Unitization.ext
      · simp only [Unitization.fst_add, Unitization.fst_smul, Unitization.fst_one,
          Unitization.fst_inr, smul_eq_mul, mul_one, add_zero]
      · simp only [Unitization.snd_add, Unitization.snd_smul, Unitization.snd_one,
          Unitization.snd_inr, smul_zero, zero_add]
  · apply sup_le
    · apply Submodule.span_le.mpr
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact (mem_positiveUnitizationDegreeFiltration F I hpos N 1).mpr
        (by simpa only [Unitization.snd_one] using (positiveIdealDegreeFiltration F I hpos N).zero_mem)
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := hy
      exact (mem_positiveUnitizationDegreeFiltration F I hpos N _).mpr ha

variable (W : DyadicDualData F) (hW : PrimalCoherent F W)
variable (hEI : allCutTwoSidedIdeal F W hW ≤ I)

def positiveUnitizationGenerator (b : Bool) :
    Unitization F (PositiveWordIdealQuotient F I hpos) :=
  Unitization.inr (positiveIdealGenerator F I hpos W hW hEI b)

theorem positiveUnitization_two_generated :
    Algebra.adjoin F (Set.range (positiveUnitizationGenerator F I hpos W hW hEI)) = ⊤ := by
  let S := Algebra.adjoin F (Set.range (positiveUnitizationGenerator F I hpos W hW hEI))
  let T := S.toNonUnitalSubalgebra.comap
    (Unitization.inrNonUnitalAlgHom F (PositiveWordIdealQuotient F I hpos))
  have hT : NonUnitalAlgebra.adjoin F
      (Set.range (positiveIdealGenerator F I hpos W hW hEI)) ≤ T := by
    apply NonUnitalAlgebra.adjoin_le
    rintro a ⟨b, rfl⟩
    exact Algebra.subset_adjoin ⟨b, rfl⟩
  rw [positiveWordIdealQuotient_two_generated F I hpos W hW hEI] at hT
  apply eq_top_iff.mpr
  intro x _
  have hsnd : (x.snd : Unitization F (PositiveWordIdealQuotient F I hpos)) ∈ S :=
    hT (show x.snd ∈ (⊤ : NonUnitalSubalgebra F (PositiveWordIdealQuotient F I hpos))
      from trivial)
  have hscalar := S.algebraMap_mem x.fst
  have hsum := S.add_mem hscalar hsnd
  change (Unitization.inl x.fst + (x.snd : Unitization F _)) ∈ S at hsum
  rw [Unitization.inl_fst_add_inr_snd_eq] at hsum
  exact hsum

def boundedPositiveUnitizedWordImage (N : ℕ) (w : BoundedPositiveWord N) :
    Unitization F (PositiveWordIdealQuotient F I hpos) :=
  Unitization.inr (boundedPositiveIdealWordImage F I hpos W hW hEI N w)

/-- The actual cutoff equals the empty-word-plus-nonempty-word span of its
actual two generators; bounded positive words already have literal products. -/
theorem positiveUnitizationDegreeFiltration_eq_wordSpan (N : ℕ) :
    positiveUnitizationDegreeFiltration F I hpos N =
      Submodule.span F (Set.insert 1
        (Set.range (boundedPositiveUnitizedWordImage F I hpos W hW hEI N))) := by
  rw [positiveUnitizationDegreeFiltration_eq_scalar_sup,
    positiveIdealDegreeFiltration_eq_wordFiltration F I hpos W hW hEI N]
  unfold positiveIdealWordFiltration
  rw [Submodule.map_span]
  have himage : (Unitization.inrHom F (PositiveWordIdealQuotient F I hpos)) ''
      Set.range (boundedPositiveIdealWordImage F I hpos W hW hEI N) =
      Set.range (boundedPositiveUnitizedWordImage F I hpos W hW hEI N) := by
    ext x
    constructor
    · rintro ⟨a, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨_, ⟨w, rfl⟩, rfl⟩
  rw [himage, ← Submodule.span_union]
  congr 1

#print axioms CriticalGK2.Actual.positiveUnitizationWordQuotientEquiv
#print axioms CriticalGK2.Actual.positiveUnitization_not_finite
#print axioms CriticalGK2.Actual.positiveUnitizationDegreeGrowth_eq
#print axioms CriticalGK2.Actual.positiveUnitization_two_generated
#print axioms CriticalGK2.Actual.positiveUnitizationDegreeFiltration_eq_wordSpan

end

end CriticalGK2.Actual
