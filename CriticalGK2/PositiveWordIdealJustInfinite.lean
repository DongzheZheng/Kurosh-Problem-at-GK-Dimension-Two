import CriticalGK2.WordIdealDegreeProjection
import CriticalGK2.PositiveWordIdealGrowth
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Graded just infinitude of the actual positive further quotient

A homogeneous F-linear ideal J of the actual positive quotient is given
as a literal submodule, closed under multiplication on both sides, whose
homogeneous intersections span J. Its image in B = H/I is a genuine
two-sided ideal because B = F*1 + Q. The preimage in H is homogeneous:
the actual descended coefficient projections preserve the image of J.
For nonzero J this preimage strictly contains I. Finite dimensionality of
strict homogeneous further quotients therefore makes Q/J finite
dimensional, through a proved injective quotient linear map.

The maximality input is the ordinary conclusion already obtained from
the actual Zorn construction. The Q-ideal, its ambient ideal, and the
embedding of Q/J are built here; none is supplied as a certificate.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]
variable (I : TwoSidedIdeal (WordAlgebra F))
variable (hpos : ∀ P : WordAlgebra F, P ∈ I → augmentation F P = 0)

def positiveIdealAmbientSpace (J : Submodule F (PositiveWordIdealQuotient F I hpos)) :
    Submodule F (WordIdealQuotient F I) :=
  J.map (positiveWordIdealLinearInclusion F I hpos)

theorem positiveIdealAmbientSpace_mul_left
    (J : Submodule F (PositiveWordIdealQuotient F I hpos))
    (hleft : ∀ a b : PositiveWordIdealQuotient F I hpos, b ∈ J → a * b ∈ J)
    (b x : WordIdealQuotient F I) (hx : x ∈ positiveIdealAmbientSpace F I hpos J) :
    b * x ∈ positiveIdealAmbientSpace F I hpos J := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨c, s, hb⟩ := positiveWordIdeal_scalar_split F I hpos b
  change b * a.val ∈ positiveIdealAmbientSpace F I hpos J
  rw [hb, add_mul, smul_mul_assoc, one_mul]
  apply (positiveIdealAmbientSpace F I hpos J).add_mem
  · exact Submodule.mem_map.mpr ⟨c • a, J.smul_mem c ha, rfl⟩
  · exact Submodule.mem_map.mpr ⟨s * a, hleft s a ha, rfl⟩

theorem positiveIdealAmbientSpace_mul_right
    (J : Submodule F (PositiveWordIdealQuotient F I hpos))
    (hright : ∀ a b : PositiveWordIdealQuotient F I hpos, a ∈ J → a * b ∈ J)
    (x b : WordIdealQuotient F I) (hx : x ∈ positiveIdealAmbientSpace F I hpos J) :
    x * b ∈ positiveIdealAmbientSpace F I hpos J := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨c, s, hb⟩ := positiveWordIdeal_scalar_split F I hpos b
  change a.val * b ∈ positiveIdealAmbientSpace F I hpos J
  rw [hb, mul_add, mul_smul_comm, mul_one]
  apply (positiveIdealAmbientSpace F I hpos J).add_mem
  · exact Submodule.mem_map.mpr ⟨c • a, J.smul_mem c ha, rfl⟩
  · exact Submodule.mem_map.mpr ⟨a * s, hright a s ha, rfl⟩

def positiveIdealAmbientIdeal
    (J : Submodule F (PositiveWordIdealQuotient F I hpos))
    (hleft : ∀ a b : PositiveWordIdealQuotient F I hpos, b ∈ J → a * b ∈ J)
    (hright : ∀ a b : PositiveWordIdealQuotient F I hpos, a ∈ J → a * b ∈ J) :
    TwoSidedIdeal (WordIdealQuotient F I) :=
  TwoSidedIdeal.mk' (positiveIdealAmbientSpace F I hpos J : Set _)
    (positiveIdealAmbientSpace F I hpos J).zero_mem
    (fun hx hy => (positiveIdealAmbientSpace F I hpos J).add_mem hx hy)
    (fun hx => (positiveIdealAmbientSpace F I hpos J).neg_mem hx)
    (fun {b x} hx => positiveIdealAmbientSpace_mul_left F I hpos J hleft b x hx)
    (fun {x b} hx => positiveIdealAmbientSpace_mul_right F I hpos J hright x b hx)

@[simp]
theorem mem_positiveIdealAmbientIdeal
    (J : Submodule F (PositiveWordIdealQuotient F I hpos))
    (hleft : ∀ a b : PositiveWordIdealQuotient F I hpos, b ∈ J → a * b ∈ J)
    (hright : ∀ a b : PositiveWordIdealQuotient F I hpos, a ∈ J → a * b ∈ J)
    (b : WordIdealQuotient F I) :
    b ∈ positiveIdealAmbientIdeal F I hpos J hleft hright ↔
      b ∈ positiveIdealAmbientSpace F I hpos J := by
  simp only [positiveIdealAmbientIdeal, TwoSidedIdeal.mem_mk']
  rfl

def positiveIdealPreimage
    (J : Submodule F (PositiveWordIdealQuotient F I hpos))
    (hleft : ∀ a b : PositiveWordIdealQuotient F I hpos, b ∈ J → a * b ∈ J)
    (hright : ∀ a b : PositiveWordIdealQuotient F I hpos, a ∈ J → a * b ∈ J) :
    TwoSidedIdeal (WordAlgebra F) :=
  (positiveIdealAmbientIdeal F I hpos J hleft hright).comap
    (wordIdealQuotientMap F I).toRingHom

theorem ideal_le_positiveIdealPreimage
    (J : Submodule F (PositiveWordIdealQuotient F I hpos))
    (hleft : ∀ a b : PositiveWordIdealQuotient F I hpos, b ∈ J → a * b ∈ J)
    (hright : ∀ a b : PositiveWordIdealQuotient F I hpos, a ∈ J → a * b ∈ J) :
    I ≤ positiveIdealPreimage F I hpos J hleft hright := by
  intro P hP
  change wordIdealQuotientMap F I P ∈ positiveIdealAmbientIdeal F I hpos J hleft hright
  rw [(wordIdealQuotientMap_eq_zero_iff F I P).mpr hP]
  exact (positiveIdealAmbientIdeal F I hpos J hleft hright).zero_mem

theorem ideal_lt_positiveIdealPreimage
    (J : Submodule F (PositiveWordIdealQuotient F I hpos))
    (hleft : ∀ a b : PositiveWordIdealQuotient F I hpos, b ∈ J → a * b ∈ J)
    (hright : ∀ a b : PositiveWordIdealQuotient F I hpos, a ∈ J → a * b ∈ J)
    (hJ : J ≠ ⊥) : I < positiveIdealPreimage F I hpos J hleft hright := by
  apply lt_of_le_of_ne (ideal_le_positiveIdealPreimage F I hpos J hleft hright)
  intro heq
  obtain ⟨a, ha, hane⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  obtain ⟨P, hP⟩ := wordIdealQuotientMap_surjective F I a.val
  have hPL : P ∈ positiveIdealPreimage F I hpos J hleft hright := by
    change wordIdealQuotientMap F I P ∈ positiveIdealAmbientIdeal F I hpos J hleft hright
    rw [hP, mem_positiveIdealAmbientIdeal]
    exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩
  have hPI : P ∈ I := by rw [heq]; exact hPL
  have haz : a.val = 0 := hP.symm.trans ((wordIdealQuotientMap_eq_zero_iff F I P).mpr hPI)
  exact hane (Subtype.ext haz)

theorem positiveIdealAmbientSpace_degreeProjection_mem
    (hhom : WordIdealHomogeneous F I)
    (J : Submodule F (PositiveWordIdealQuotient F I hpos))
    (hJhom : J = ⨆ n : ℕ, J ⊓ positiveIdealDegreeSpace F I hpos n)
    (m : ℕ) (b : WordIdealQuotient F I)
    (hb : b ∈ positiveIdealAmbientSpace F I hpos J) :
    wordIdealDegreeProjection F I hhom m b ∈ positiveIdealAmbientSpace F I hpos J := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hb
  have hle : J ≤ (positiveIdealAmbientSpace F I hpos J).comap
      ((wordIdealDegreeProjection F I hhom m).comp
        (positiveWordIdealLinearInclusion F I hpos)) := by
    calc
      J = ⨆ n : ℕ, J ⊓ positiveIdealDegreeSpace F I hpos n := hJhom
      _ ≤ _ := by
        apply iSup_le
        intro n a ha
        have hdegree : a.val ∈ CriticalGK2.HomogeneousGrading.degreeSpace F I (n + 1) :=
          ha.2
        change wordIdealDegreeProjection F I hhom m a.val ∈ positiveIdealAmbientSpace F I hpos J
        rw [wordIdealDegreeProjection_of_degreeSpace F I hhom m (n + 1) a.val hdegree]
        by_cases hnm : n + 1 = m
        · rw [if_pos hnm]
          exact Submodule.mem_map.mpr ⟨a, ha.1, rfl⟩
        · rw [if_neg hnm]
          exact (positiveIdealAmbientSpace F I hpos J).zero_mem
  exact hle ha

theorem positiveIdealPreimage_homogeneous
    (hhom : WordIdealHomogeneous F I)
    (J : Submodule F (PositiveWordIdealQuotient F I hpos))
    (hleft : ∀ a b : PositiveWordIdealQuotient F I hpos, b ∈ J → a * b ∈ J)
    (hright : ∀ a b : PositiveWordIdealQuotient F I hpos, a ∈ J → a * b ∈ J)
    (hJhom : J = ⨆ n : ℕ, J ⊓ positiveIdealDegreeSpace F I hpos n) :
    WordIdealHomogeneous F (positiveIdealPreimage F I hpos J hleft hright) := by
  intro m P hP
  change wordIdealQuotientMap F I P ∈ positiveIdealAmbientIdeal F I hpos J hleft hright at hP
  change wordIdealQuotientMap F I (degreeProjection F m P) ∈
    positiveIdealAmbientIdeal F I hpos J hleft hright
  rw [mem_positiveIdealAmbientIdeal, ← wordIdealDegreeProjection_map F I hhom]
  exact positiveIdealAmbientSpace_degreeProjection_mem F I hpos hhom J hJhom m _
    ((mem_positiveIdealAmbientIdeal F I hpos J hleft hright _).mp hP)

def wordIdealFurtherFactor (L : TwoSidedIdeal (WordAlgebra F)) (hIL : I ≤ L) :
    WordIdealQuotient F I →ₐ[F] WordIdealQuotient F L :=
  RingCon.factorₐ F (TwoSidedIdeal.ringCon_le_iff.mp hIL)

@[simp]
theorem wordIdealFurtherFactor_map (L : TwoSidedIdeal (WordAlgebra F)) (hIL : I ≤ L)
    (P : WordAlgebra F) :
    wordIdealFurtherFactor F I L hIL (wordIdealQuotientMap F I P) = wordIdealQuotientMap F L P := rfl

def positiveIdealFurtherLinearMap
    (J : Submodule F (PositiveWordIdealQuotient F I hpos))
    (hleft : ∀ a b : PositiveWordIdealQuotient F I hpos, b ∈ J → a * b ∈ J)
    (hright : ∀ a b : PositiveWordIdealQuotient F I hpos, a ∈ J → a * b ∈ J) :
    PositiveWordIdealQuotient F I hpos →ₗ[F]
      WordIdealQuotient F (positiveIdealPreimage F I hpos J hleft hright) :=
  (wordIdealFurtherFactor F I _ (ideal_le_positiveIdealPreimage F I hpos J hleft hright)).toLinearMap.comp
    (positiveWordIdealLinearInclusion F I hpos)

theorem positiveIdealFurtherLinearMap_eq_zero_iff
    (J : Submodule F (PositiveWordIdealQuotient F I hpos))
    (hleft : ∀ a b : PositiveWordIdealQuotient F I hpos, b ∈ J → a * b ∈ J)
    (hright : ∀ a b : PositiveWordIdealQuotient F I hpos, a ∈ J → a * b ∈ J)
    (a : PositiveWordIdealQuotient F I hpos) :
    positiveIdealFurtherLinearMap F I hpos J hleft hright a = 0 ↔ a ∈ J := by
  obtain ⟨P, hP⟩ := wordIdealQuotientMap_surjective F I a.val
  have heval : positiveIdealFurtherLinearMap F I hpos J hleft hright a =
      wordIdealQuotientMap F (positiveIdealPreimage F I hpos J hleft hright) P := by
    change wordIdealFurtherFactor F I
      (positiveIdealPreimage F I hpos J hleft hright)
      (ideal_le_positiveIdealPreimage F I hpos J hleft hright) a.val = _
    rw [← hP, wordIdealFurtherFactor_map]
  rw [heval, wordIdealQuotientMap_eq_zero_iff]
  change wordIdealQuotientMap F I P ∈ positiveIdealAmbientIdeal F I hpos J hleft hright ↔ a ∈ J
  rw [hP, mem_positiveIdealAmbientIdeal]
  constructor
  · rintro ⟨b, hb, hba⟩
    have heq : b = a := positiveWordIdealLinearInclusion_injective F I hpos hba
    simpa only [heq] using hb
  · intro ha
    exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩

/-- Every actual nonzero homogeneous F-linear ideal in Q has finite codimension. -/
theorem positiveWordIdealQuotient_graded_just_infinite
    (hhom : WordIdealHomogeneous F I)
    (hfinite : ∀ L : TwoSidedIdeal (WordAlgebra F), WordIdealHomogeneous F L →
      I < L → Module.Finite F (WordIdealQuotient F L))
    (J : Submodule F (PositiveWordIdealQuotient F I hpos))
    (hJ : J ≠ ⊥)
    (hleft : ∀ a b : PositiveWordIdealQuotient F I hpos, b ∈ J → a * b ∈ J)
    (hright : ∀ a b : PositiveWordIdealQuotient F I hpos, a ∈ J → a * b ∈ J)
    (hJhom : J = ⨆ n : ℕ, J ⊓ positiveIdealDegreeSpace F I hpos n) :
    Module.Finite F ((PositiveWordIdealQuotient F I hpos) ⧸ J) := by
  let L := positiveIdealPreimage F I hpos J hleft hright
  letI : Module.Finite F (WordIdealQuotient F L) := hfinite L
    (positiveIdealPreimage_homogeneous F I hpos hhom J hleft hright hJhom)
    (ideal_lt_positiveIdealPreimage F I hpos J hleft hright hJ)
  let f := positiveIdealFurtherLinearMap F I hpos J hleft hright
  have hker : J = LinearMap.ker f := by
    apply Submodule.ext
    intro a
    exact (positiveIdealFurtherLinearMap_eq_zero_iff F I hpos J hleft hright a).symm
  let g := J.liftQ f hker.le
  have hg : Function.Injective g := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' J f hker)
  exact FiniteDimensional.of_injective g hg

#print axioms CriticalGK2.Actual.positiveIdealPreimage_homogeneous
#print axioms CriticalGK2.Actual.positiveIdealFurtherLinearMap_eq_zero_iff
#print axioms CriticalGK2.Actual.positiveWordIdealQuotient_graded_just_infinite

end

end CriticalGK2.Actual
