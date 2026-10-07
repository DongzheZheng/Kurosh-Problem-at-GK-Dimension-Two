import CriticalGK2.HomogeneousQuotientInputs

/-!
# The actual positive quotient of an arbitrary homogeneous no-tail ideal

The unital object is B = H/I. The positive non-unital object is the literal
kernel of the augmentation descended to B. An explicit hypothesis that I
lies in the original augmentation kernel is first derived from actual
homogeneity and no-tail. Operations and scalar instances are ordinary
inherited non-unital subalgebra structures.

The actual positive map from the original H-plus is proved surjective;
the actual subtype inclusion is injective; and B is explicitly decomposed
as F*1 plus the positive kernel.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

theorem homogeneousProjection_zero_single (P : WordAlgebra F) :
    (homogeneousProjection F 0 P).val = MonoidAlgebra.single 1 (P 1) := by
  classical
  apply Finsupp.ext
  intro w
  rw [homogeneousProjection_coeff]
  by_cases hw : w = 1
  · subst w
    simp only [FreeMonoid.length_one, ite_true, MonoidAlgebra.single, Finsupp.single_eq_same]
  · have hlen : w.length ≠ 0 := fun h => hw (FreeMonoid.length_eq_zero.mp h)
    rw [if_neg hlen]
    simp only [MonoidAlgebra.single, Finsupp.single_eq_of_ne hw]

/-- No-tail plus actual homogeneity rules out every nonzero scalar component. -/
theorem homogeneous_noWordTail_augmentation_eq_zero
    (I : TwoSidedIdeal (WordAlgebra F)) (hhom : WordIdealHomogeneous F I)
    (htail : NoWordTail F I) (P : WordAlgebra F) (hP : P ∈ I) : augmentation F P = 0 := by
  rw [augmentation_eq_constantCoeff]
  by_contra hc
  have hcomponent := hhom 0 P hP
  rw [homogeneousProjection_zero_single F P] at hcomponent
  have hscaled := wordIdeal_smul_mem F I (P 1)⁻¹ _ hcomponent
  have heq : (P 1)⁻¹ • (MonoidAlgebra.single (1 : Word) (P 1) : WordAlgebra F) =
      MonoidAlgebra.single (1 : Word) (1 : F) := by
    change (P 1)⁻¹ • (Finsupp.single (1 : Word) (P 1) : Word →₀ F) =
      Finsupp.single (1 : Word) (1 : F)
    rw [Finsupp.smul_single, smul_eq_mul, inv_mul_cancel₀ hc]
  rw [heq, ← MonoidAlgebra.one_def] at hscaled
  have htop : I = ⊤ := (TwoSidedIdeal.one_mem_iff I).mp hscaled
  apply htail 0
  rw [htop]
  exact le_top

variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)

include hpos in
theorem wordIdeal_congruence_le_augmentation_ker :
    I.ringCon ≤ RingCon.ker (augmentation F).toRingHom := by
  intro P Q hPQ
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact hpos (P - Q) ((I.rel_iff P Q).mp hPQ)

def wordIdealQuotientAugmentation : WordIdealQuotient F I →ₐ[F] F :=
  I.ringCon.liftₐ (augmentation F) (wordIdeal_congruence_le_augmentation_ker F I hpos)

@[simp]
theorem wordIdealQuotientAugmentation_map (P : WordAlgebra F) :
    wordIdealQuotientAugmentation F I hpos (wordIdealQuotientMap F I P) = augmentation F P := rfl

def positiveWordIdealSubalgebra : NonUnitalSubalgebra F (WordIdealQuotient F I) :=
  ((wordIdealQuotientAugmentation F I hpos).toLinearMap.ker).toNonUnitalSubalgebra
    (fun x y hx hy => by
      change wordIdealQuotientAugmentation F I hpos (x * y) = 0
      change wordIdealQuotientAugmentation F I hpos x = 0 at hx
      rw [map_mul, hx, zero_mul])

/-- Q = H-plus/I, the actual non-unital kernel subtype in B = H/I. -/
def PositiveWordIdealQuotient : Type _ := ↥(positiveWordIdealSubalgebra F I hpos)

instance positiveWordIdealQuotientNonUnitalRing : NonUnitalRing (PositiveWordIdealQuotient F I hpos) :=
  NonUnitalSubalgebra.toNonUnitalRing (positiveWordIdealSubalgebra F I hpos)

instance positiveWordIdealQuotientModule : Module F (PositiveWordIdealQuotient F I hpos) :=
  NonUnitalSubalgebra.instModule (S := positiveWordIdealSubalgebra F I hpos)

instance positiveWordIdealQuotientScalarTower :
    IsScalarTower F (PositiveWordIdealQuotient F I hpos) (PositiveWordIdealQuotient F I hpos) where
  smul_assoc c x y := Subtype.ext (smul_mul_assoc c x.val y.val)

instance positiveWordIdealQuotientSMulComm :
    SMulCommClass F (PositiveWordIdealQuotient F I hpos) (PositiveWordIdealQuotient F I hpos) where
  smul_comm c x y := Subtype.ext (mul_smul_comm c x.val y.val).symm

@[simp]
theorem mem_positiveWordIdealSubalgebra (b : WordIdealQuotient F I) :
    b ∈ positiveWordIdealSubalgebra F I hpos ↔
      wordIdealQuotientAugmentation F I hpos b = 0 := Iff.rfl

def positiveWordIdealInclusion :
    PositiveWordIdealQuotient F I hpos →ₙₐ[F] WordIdealQuotient F I where
  toFun a := a.val
  map_zero' := rfl
  map_add' a b := rfl
  map_mul' a b := rfl
  map_smul' c a := rfl

theorem positiveWordIdealInclusion_injective :
    Function.Injective (positiveWordIdealInclusion F I hpos) := Subtype.val_injective

/-- Explicit linear inclusion avoids a generic NonUnitalAlgHom class boundary. -/
def positiveWordIdealLinearInclusion :
    PositiveWordIdealQuotient F I hpos →ₗ[F] WordIdealQuotient F I where
  toFun a := a.val
  map_add' a b := rfl
  map_smul' c a := rfl

theorem positiveWordIdealLinearInclusion_injective :
    Function.Injective (positiveWordIdealLinearInclusion F I hpos) := Subtype.val_injective

def positiveWordIdealQuotientMap : positiveWordSubmodule F →ₗ[F] PositiveWordIdealQuotient F I hpos where
  toFun P := ⟨wordIdealQuotientMap F I P.val, P.property⟩
  map_add' P Q := Subtype.ext ((wordIdealQuotientMap F I).map_add P.val Q.val)
  map_smul' c P := Subtype.ext ((wordIdealQuotientMap F I).toLinearMap.map_smul c P.val)

theorem positiveWordIdealQuotientMap_surjective :
    Function.Surjective (positiveWordIdealQuotientMap F I hpos) := by
  intro a
  obtain ⟨P, hP⟩ := wordIdealQuotientMap_surjective F I a.val
  have hPpos : P ∈ positiveWordSubmodule F := by
    change augmentation F P = 0
    rw [← wordIdealQuotientAugmentation_map F I hpos, hP]
    exact a.property
  exact ⟨⟨P, hPpos⟩, Subtype.ext hP⟩

theorem positiveWordIdealSubalgebra_eq_positive_image :
    (positiveWordIdealSubalgebra F I hpos).toSubmodule =
      (positiveWordSubmodule F).map (wordIdealQuotientMap F I).toLinearMap := by
  apply Submodule.ext
  intro b
  constructor
  · intro hb
    obtain ⟨P, rfl⟩ := wordIdealQuotientMap_surjective F I b
    exact ⟨P, hb, rfl⟩
  · rintro ⟨P, hP, rfl⟩
    exact hP

/-- The true scalar-plus-positive decomposition used in prime inheritance. -/
theorem positiveWordIdeal_scalar_split (b : WordIdealQuotient F I) :
    ∃ c : F, ∃ a : PositiveWordIdealQuotient F I hpos, b = c • (1 : WordIdealQuotient F I) + a.val := by
  let c := wordIdealQuotientAugmentation F I hpos b
  let a : PositiveWordIdealQuotient F I hpos := ⟨b - c • 1, by
    change wordIdealQuotientAugmentation F I hpos (b - c • 1) = 0
    rw [map_sub, map_smul, map_one]
    simp only [smul_eq_mul, mul_one, c, sub_self]⟩
  refine ⟨c, a, ?_⟩
  change b = c • 1 + (b - c • 1)
  abel

theorem positiveWordIdealQuotient_nonzero (htail : NoWordTail F I) :
    ∃ a : PositiveWordIdealQuotient F I hpos, a ≠ 0 := by
  classical
  have hex : ∃ w : LengthWord 1, wordIdealQuotientMap F I (MonoidAlgebra.single w.val 1) ≠ 0 := by
    by_contra h
    apply htail 1
    apply wordTailIdeal_le_of_length_monomials F I 1
    intro w
    apply (wordIdealQuotientMap_eq_zero_iff F I _).mp
    by_contra hw
    exact h ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hex
  let P : positiveWordSubmodule F := ⟨MonoidAlgebra.single w.val 1,
    augmentation_homogeneous_eq_zero F 1 (by omega) _ (monomial_mem_homogeneous F 1 w 1)⟩
  refine ⟨positiveWordIdealQuotientMap F I hpos P, ?_⟩
  intro hzero
  exact hw (congrArg (fun a : PositiveWordIdealQuotient F I hpos => a.val) hzero)

#print axioms CriticalGK2.Actual.homogeneous_noWordTail_augmentation_eq_zero
#print axioms CriticalGK2.Actual.positiveWordIdealQuotientMap_surjective
#print axioms CriticalGK2.Actual.positiveWordIdeal_scalar_split
#print axioms CriticalGK2.Actual.positiveWordIdealQuotient_nonzero

end

end CriticalGK2.Actual
