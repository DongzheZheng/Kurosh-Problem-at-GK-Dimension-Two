import CriticalGK2.NormalWordFactorial
import CriticalGK2.WordTensor
import CriticalGK2.PositiveComponents
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Actual finite greedy normal-word basis and component dimensions

The generic finite greedy lemma selects vectors by nonmembership in the
span of strictly smaller literal natural-number codes. Independence is
proved by maximal-element induction, and spanning by induction on those
codes. The chosen family is instantiated with actual coefficient-one word
images in the actual all-cut quotient. Its cardinality is identified with
the actual H_n/E_n quotient dimension using its actual kernel.
-/

namespace CriticalGK2.Greedy

open scoped BigOperators

noncomputable section

variable (F : Type*) [Field F] {ι X : Type*} [AddCommGroup X] [Module F X]

/-- Actual earlier vectors according to the supplied actual natural-number code. -/
def Earlier (f : ι → X) (c : ι → ℕ) (i : ι) : Set X :=
  {z | ∃ j : ι, c j < c i ∧ f j = z}

/-- The finite greedy selection criterion. -/
def Good (f : ι → X) (c : ι → ℕ) (i : ι) : Prop :=
  f i ∉ Submodule.span F (Earlier f c i)

/-- The actual selected subfamily. -/
def Index (f : ι → X) (c : ι → ℕ) := {i : ι // Good F f c i}

instance indexFintype [Fintype ι] (f : ι → X) (c : ι → ℕ) : Fintype (Index F f c) := by
  classical
  change Fintype {i : ι // Good F f c i}
  infer_instance

def family (f : ι → X) (c : ι → ℕ) : Index F f c → X := fun i => f i.val

/-- Any finite selected set is independent. Only the literal injectivity of
codes is required; the entire actual greedy criterion is expanded in the proof. -/
theorem finite_good_linearIndepOn (f : ι → X) (c : ι → ℕ) (hc : Function.Injective c)
    (s : Finset ι) (hs : ∀ i ∈ s, Good F f c i) : LinearIndepOn F f (s : Set ι) := by
  classical
  letI : LinearOrder ι := LinearOrder.lift' c hc
  revert hs
  induction s using Finset.induction_on_max with
  | empty =>
      intro hs
      simpa using linearIndepOn_empty F f
  | insert a s hmax ih =>
      intro hs
      have hss : ∀ i ∈ s, Good F f c i := fun i hi => hs i (Finset.mem_insert_of_mem hi)
      have ha : Good F f c a := hs a (Finset.mem_insert_self a s)
      have hle : Submodule.span F (f '' (s : Set ι)) ≤ Submodule.span F (Earlier f c a) := by
        apply Submodule.span_mono
        rintro z ⟨i, hi, rfl⟩
        exact ⟨i, hmax i hi, rfl⟩
      have hnot : f a ∉ Submodule.span F (f '' (s : Set ι)) := fun h => ha (hle h)
      simpa only [Finset.coe_insert] using (ih hss).insert hnot

/-- Independence of the complete actual finite greedy subfamily. -/
theorem family_linearIndependent [Fintype ι]
    (f : ι → X) (c : ι → ℕ) (hc : Function.Injective c) :
    LinearIndependent F (family F f c) := by
  classical
  let s : Finset ι := Finset.univ.filter (Good F f c)
  have hs : ∀ i ∈ s, Good F f c i := fun i hi => (Finset.mem_filter.mp hi).2
  have h := finite_good_linearIndepOn F f c hc s hs
  have he : (s : Set ι) = {i : ι | Good F f c i} := by ext i; simp [s]
  rw [he] at h
  exact h

/-- Every original vector belongs to the span of the selected family,
by well-founded induction on its code. -/
theorem mem_span_family (f : ι → X) (c : ι → ℕ) (i : ι) :
    f i ∈ Submodule.span F (Set.range (family F f c)) := by
  classical
  have hm : ∀ m : ℕ, ∀ i : ι, c i = m →
      f i ∈ Submodule.span F (Set.range (family F f c)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro i hi
        by_cases hg : Good F f c i
        · exact Submodule.subset_span ⟨⟨i, hg⟩, rfl⟩
        · have hmem : f i ∈ Submodule.span F (Earlier f c i) := by
            simpa only [Good, not_not] using hg
          have hle : Submodule.span F (Earlier f c i) ≤
              Submodule.span F (Set.range (family F f c)) := by
            apply Submodule.span_le.mpr
            rintro z ⟨j, hj, rfl⟩
            exact ih (c j) (by rw [← hi]; exact hj) j rfl
          exact hle hmem
  exact hm (c i) i rfl

/-- Exact equality of spans, proved from the actual selected vectors. -/
theorem span_family_eq_span (f : ι → X) (c : ι → ℕ) :
    Submodule.span F (Set.range (family F f c)) = Submodule.span F (Set.range f) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i.val, rfl⟩
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    exact mem_span_family F f c i

/-- Pivot counting for the actual finite greedy selection. -/
theorem card_index_eq_finrank_span [Fintype ι]
    (f : ι → X) (c : ι → ℕ) (hc : Function.Injective c) :
    Fintype.card (Index F f c) = Module.finrank F (Submodule.span F (Set.range f)) := by
  have h := (linearIndependent_iff_card_eq_finrank_span).mp
    (family_linearIndependent F f c hc)
  change Fintype.card (Index F f c) =
    Module.finrank F (Submodule.span F (Set.range (family F f c))) at h
  rw [span_family_eq_span] at h
  exact h

end

end CriticalGK2.Greedy

namespace CriticalGK2.Actual

open CriticalGK2.WordOrder
open scoped BigOperators

noncomputable section

variable (F : Type*) [Field F]

/-- The same actual normal word criterion as a finite actual selected family. -/
def NormalLengthWord (W : DyadicDualData F) (hW : PrimalCoherent F W) (n : ℕ) :=
  CriticalGK2.Greedy.Index F (fun w : LengthWord n => quotientWord F W hW w.val)
    (fun w : LengthWord n => wordNumber w.val)

instance normalLengthWordFintype (W : DyadicDualData F) (hW : PrimalCoherent F W) (n : ℕ) :
    Fintype (NormalLengthWord F W hW n) :=
  CriticalGK2.Greedy.indexFintype F _ _

theorem greedyEarlier_eq_earlierWordImages (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (w : LengthWord n) :
    CriticalGK2.Greedy.Earlier (fun v : LengthWord n => quotientWord F W hW v.val)
      (fun v : LengthWord n => wordNumber v.val) w = earlierWordImages F W hW w.val := by
  ext z
  constructor
  · rintro ⟨v, hcode, hz⟩
    exact ⟨v.val, v.property.trans w.property.symm, hcode, hz⟩
  · rintro ⟨v, hlen, hcode, hz⟩
    exact ⟨⟨v, hlen.trans w.property⟩, hcode, hz⟩

theorem normalLengthWord_is_normal (W : DyadicDualData F) (hW : PrimalCoherent F W)
    (n : ℕ) (w : NormalLengthWord F W hW n) : NormalWord F W hW w.val.val := by
  have hw := w.property
  change quotientWord F W hW w.val.val ∉ Submodule.span F
    (CriticalGK2.Greedy.Earlier (fun v : LengthWord n => quotientWord F W hW v.val)
      (fun v : LengthWord n => wordNumber v.val) w.val) at hw
  rw [greedyEarlier_eq_earlierWordImages] at hw
  exact hw

/-- Actual selected singleton quotient images, with the actual word basis index. -/
def normalWordFamily (W : DyadicDualData F) (hW : PrimalCoherent F W) (n : ℕ) :
    NormalLengthWord F W hW n → AllCutRingQuotient F W hW :=
  fun w => quotientWord F W hW w.val.val

theorem normalWordFamily_linearIndependent (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) : LinearIndependent F (normalWordFamily F W hW n) :=
  CriticalGK2.Greedy.family_linearIndependent F
    (fun w : LengthWord n => quotientWord F W hW w.val)
    (fun w : LengthWord n => wordNumber w.val) (lengthWordNumber_injective n)

theorem normalWordFamily_span (W : DyadicDualData F) (hW : PrimalCoherent F W) (n : ℕ) :
    Submodule.span F (Set.range (normalWordFamily F W hW n)) =
      Submodule.span F (Set.range (fun w : LengthWord n => quotientWord F W hW w.val)) :=
  CriticalGK2.Greedy.span_family_eq_span F
    (fun w : LengthWord n => quotientWord F W hW w.val)
    (fun w : LengthWord n => wordNumber w.val)

/-- Actual homogeneous projection to the original ring quotient. -/
def homogeneousWordQuotientMap (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) : homogeneous F n →ₗ[F] AllCutRingQuotient F W hW :=
  (allCutQuotientMap F W hW).toLinearMap.comp (homogeneous F n).subtype

@[simp]
theorem homogeneousWordQuotientMap_basis (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (w : LengthWord n) :
    homogeneousWordQuotientMap F W hW n (homogeneousWordBasis F n w) =
      quotientWord F W hW w.val := by
  change allCutQuotientMap F W hW ((homogeneousWordBasis F n w).val) = _
  rw [homogeneousWordBasis_coe]
  rfl

/-- The actual kernel is the actual E_n, using the previously proved original
same-degree intersection equality. -/
theorem homogeneousWordQuotientMap_ker (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) :
    (homogeneousWordQuotientMap F W hW n).ker =
      (allCutComponent F W n).comap (homogeneous F n).subtype := by
  rw [← allCutSubmodule_comap_homogeneous F W n]
  apply Submodule.ext
  intro x
  exact allCutQuotientMap_eq_zero_iff F W hW x.val

/-- Exact word-image span identification for the actual homogeneous image. -/
theorem homogeneousWordImage_span_eq_range (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) :
    Submodule.span F (Set.range (fun w : LengthWord n => quotientWord F W hW w.val)) =
      LinearMap.range (homogeneousWordQuotientMap F W hW n) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨w, rfl⟩
    exact ⟨homogeneousWordBasis F n w, homogeneousWordQuotientMap_basis F W hW n w⟩
  · rintro z ⟨x, rfl⟩
    rw [← (homogeneousWordBasis F n).sum_repr x, map_sum]
    apply Submodule.sum_mem
    intro w _
    rw [map_smul, homogeneousWordQuotientMap_basis]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)

/-- The literal actual H_n/E_n is isomorphic to the literal word-image subspace. -/
def componentQuotientEquivWordImage (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) :
    ComponentQuotient F W n ≃ₗ[F] LinearMap.range (homogeneousWordQuotientMap F W hW n) := by
  change (homogeneous F n ⧸ (allCutComponent F W n).comap (homogeneous F n).subtype) ≃ₗ[F] _
  rw [← homogeneousWordQuotientMap_ker]
  exact (homogeneousWordQuotientMap F W hW n).quotKerEquivRange

/-- The pivot count equals the dimension of the component quotient. -/
theorem card_normalLengthWord_eq_componentQuotient_finrank (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) :
    Fintype.card (NormalLengthWord F W hW n) = Module.finrank F (ComponentQuotient F W n) := by
  have h := CriticalGK2.Greedy.card_index_eq_finrank_span F
    (fun w : LengthWord n => quotientWord F W hW w.val)
    (fun w : LengthWord n => wordNumber w.val) (lengthWordNumber_injective n)
  rw [homogeneousWordImage_span_eq_range] at h
  exact h.trans (componentQuotientEquivWordImage F W hW n).finrank_eq.symm

/-- Actual homogeneous survival gives an actual normal word of that degree. -/
theorem exists_normalWord_of_homogeneous_survival (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (x : homogeneous F n)
    (hx : homogeneousWordQuotientMap F W hW n x ≠ 0) :
    ∃ w : LengthWord n, NormalWord F W hW w.val := by
  classical
  have hn : Nonempty (NormalLengthWord F W hW n) := by
    by_contra h
    letI : IsEmpty (NormalLengthWord F W hW n) := ⟨fun w => h ⟨w⟩⟩
    have he : Submodule.span F (Set.range (normalWordFamily F W hW n)) = ⊥ := by simp
    have hr : LinearMap.range (homogeneousWordQuotientMap F W hW n) = ⊥ := by
      rw [← homogeneousWordImage_span_eq_range, ← normalWordFamily_span, he]
    have hm : homogeneousWordQuotientMap F W hW n x ∈
        LinearMap.range (homogeneousWordQuotientMap F W hW n) := ⟨x, rfl⟩
    rw [hr] at hm
    exact hx hm
  obtain ⟨w⟩ := hn
  exact ⟨w.val, normalLengthWord_is_normal F W hW n w⟩

/-- The already proved actual positive-degree survival instantiates the
normal-word existence statement at the literal dyadic construction. -/
theorem exists_normalWord_of_root_ne_bot (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : n ≠ 0)
    (hroot : W (strictDyadicRoot n) ≠ ⊥) :
    ∃ w : LengthWord n, NormalWord F W hW w.val := by
  obtain ⟨x, hx, hq⟩ := exists_homogeneous_quotient_ne_zero F W hW n hn hroot
  exact exists_normalWord_of_homogeneous_survival F W hW n ⟨x, hx⟩ hq

#print axioms CriticalGK2.Greedy.family_linearIndependent
#print axioms CriticalGK2.Greedy.card_index_eq_finrank_span
#print axioms CriticalGK2.Actual.card_normalLengthWord_eq_componentQuotient_finrank
#print axioms CriticalGK2.Actual.exists_normalWord_of_root_ne_bot

end

end CriticalGK2.Actual
