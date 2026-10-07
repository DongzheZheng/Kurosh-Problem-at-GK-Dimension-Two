import CriticalGK2.HomogeneousQuotientInputs
import CriticalGK2.PositiveGradedSum

/-!
# Actual cumulative growth after an arbitrary homogeneous quotient

The positive degree spaces are the literal images of H_n in H/I. Finite
homogeneous independence is proved by lifting to H and projecting a relation
back through the actual homogeneous ideal I. In particular the lower growth
bound after taking a further quotient is proved for that new quotient.
-/

namespace CriticalGK2.Actual

noncomputable section

open scoped BigOperators

variable (F : Type*) [Field F]

def idealDegreeSpace (I : TwoSidedIdeal (WordAlgebra F)) (n : ℕ) :
    Submodule F (WordIdealQuotient F I) :=
  CriticalGK2.GenericLower.degreeImage F (wordIdealQuotientMap F I) n

instance idealDegreeSpace_finite (I : TwoSidedIdeal (WordAlgebra F)) (n : ℕ) :
    FiniteDimensional F (idealDegreeSpace F I n) :=
  inferInstanceAs (FiniteDimensional F
    (CriticalGK2.GenericLower.degreeImage F (wordIdealQuotientMap F I) n))

def idealPositiveDegreeFiltration (I : TwoSidedIdeal (WordAlgebra F)) (N : ℕ) :
    Submodule F (WordIdealQuotient F I) :=
  (Finset.range N).sup (fun m => idealDegreeSpace F I (m + 1))

instance idealPositiveDegreeFiltration_finite (I : TwoSidedIdeal (WordAlgebra F)) (N : ℕ) :
    FiniteDimensional F (idealPositiveDegreeFiltration F I N) := by
  unfold idealPositiveDegreeFiltration
  infer_instance

def idealPositiveDegreeGrowth (I : TwoSidedIdeal (WordAlgebra F)) (N : ℕ) : ℕ :=
  Module.finrank F (idealPositiveDegreeFiltration F I N)

def idealFiniteDegreeSumMap (I : TwoSidedIdeal (WordAlgebra F)) (N : ℕ) :
    (∀ i : Fin N, idealDegreeSpace F I (i.val + 1)) →ₗ[F] WordIdealQuotient F I where
  toFun x := ∑ i, (x i).val
  map_add' x y := by simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply]
    exact Finset.smul_sum.symm

theorem idealFiniteDegreeSumMap_eq_zero_iff (I : TwoSidedIdeal (WordAlgebra F))
    (hhom : WordIdealHomogeneous F I) (N : ℕ)
    (x : ∀ i : Fin N, idealDegreeSpace F I (i.val + 1)) :
    idealFiniteDegreeSumMap F I N x = 0 ↔ x = 0 := by
  classical
  constructor
  · intro hzero
    have hex : ∀ i : Fin N, ∃ y : WordAlgebra F,
        y ∈ homogeneous F (i.val + 1) ∧ wordIdealQuotientMap F I y = (x i).val := by
      intro i
      exact Submodule.mem_map.mp (x i).property
    choose y hy hq using hex
    have hI : (∑ i : Fin N, y i) ∈ I := by
      apply (wordIdealQuotientMap_eq_zero_iff F I _).mp
      rw [map_sum]
      simpa only [hq] using hzero
    funext i
    let p : WordAlgebra F →ₗ[F] WordAlgebra F :=
      (homogeneous F (i.val + 1)).subtype.comp (homogeneousProjection F (i.val + 1))
    have hp : ∀ j : Fin N, p (y j) = if j = i then y i else 0 := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [p, LinearMap.comp_apply, Submodule.subtype_apply,
          homogeneousProjection_of_mem F (i.val + 1) (y i) (hy i), ite_true]
      · have hdegree : j.val + 1 ≠ i.val + 1 := by
          intro he
          apply hji
          apply Fin.ext
          omega
        simp only [p, LinearMap.comp_apply, Submodule.subtype_apply,
          homogeneousProjection_of_other_degree F (j.val + 1) (i.val + 1)
            hdegree (y j) (hy j), if_neg hji]
    have hproject : (homogeneousProjection F (i.val + 1) (∑ j : Fin N, y j)).val = y i := by
      change p (∑ j : Fin N, y j) = _
      simp only [map_sum, hp]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · intro hnot
        exact (hnot (Finset.mem_univ i)).elim
    have hyI := hhom (i.val + 1) _ hI
    rw [hproject] at hyI
    apply Subtype.ext
    change (x i).val = 0
    rw [← hq i]
    exact (wordIdealQuotientMap_eq_zero_iff F I _).mpr hyI
  · intro hz
    rw [hz, map_zero]

theorem idealFiniteDegreeSumMap_injective (I : TwoSidedIdeal (WordAlgebra F))
    (hhom : WordIdealHomogeneous F I) (N : ℕ) :
    Function.Injective (idealFiniteDegreeSumMap F I N) := by
  intro x y he
  have hz : idealFiniteDegreeSumMap F I N (x - y) = 0 := by
    rw [(idealFiniteDegreeSumMap F I N).map_sub, he, sub_self]
  exact sub_eq_zero.mp ((idealFiniteDegreeSumMap_eq_zero_iff F I hhom N (x - y)).mp hz)

theorem idealFiniteDegreeSumMap_range_le_filtration (I : TwoSidedIdeal (WordAlgebra F))
    (N : ℕ) : LinearMap.range (idealFiniteDegreeSumMap F I N) ≤
      idealPositiveDegreeFiltration F I N := by
  classical
  rintro a ⟨x, rfl⟩
  change (∑ i : Fin N, (x i).val) ∈ _
  apply Submodule.sum_mem
  intro i _
  have hle : idealDegreeSpace F I (i.val + 1) ≤ idealPositiveDegreeFiltration F I N :=
    Finset.le_sup (f := fun m => idealDegreeSpace F I (m + 1))
      (Finset.mem_range.mpr i.isLt)
  exact hle (x i).property

theorem ideal_component_sum_le_growth (I : TwoSidedIdeal (WordAlgebra F))
    (hhom : WordIdealHomogeneous F I) (N : ℕ) :
    (∑ i : Fin N, Module.finrank F (idealDegreeSpace F I (i.val + 1))) ≤
      idealPositiveDegreeGrowth F I N := by
  letI : ∀ i : Fin N, FiniteDimensional F (idealDegreeSpace F I (i.val + 1)) :=
    fun _ => inferInstance
  letI : ∀ i : Fin N, Module.Free F (idealDegreeSpace F I (i.val + 1)) :=
    fun i => Module.Free.of_basis (Module.Basis.ofVectorSpace F (idealDegreeSpace F I (i.val + 1)))
  calc
    _ = Module.finrank F (∀ i : Fin N, idealDegreeSpace F I (i.val + 1)) :=
      (Module.finrank_pi_fintype F).symm
    _ = Module.finrank F (LinearMap.range (idealFiniteDegreeSumMap F I N)) :=
      (LinearMap.finrank_range_of_inj (idealFiniteDegreeSumMap_injective F I hhom N)).symm
    _ ≤ idealPositiveDegreeGrowth F I N :=
      Submodule.finrank_mono (idealFiniteDegreeSumMap_range_le_filtration F I N)

theorem idealPositiveDegreeGrowth_eq_component_sum (I : TwoSidedIdeal (WordAlgebra F))
    (hhom : WordIdealHomogeneous F I) (N : ℕ) :
    idealPositiveDegreeGrowth F I N =
      ∑ m ∈ Finset.range N, Module.finrank F (idealDegreeSpace F I (m + 1)) := by
  apply Nat.le_antisymm
  · exact finite_subspace_finrank_sup_le_sum F (fun m => idealDegreeSpace F I (m + 1))
      (Finset.range N)
  · have hs := Fin.sum_univ_eq_sum_range
      (fun m : ℕ => Module.finrank F (idealDegreeSpace F I (m + 1))) N
    rw [← hs]
    exact ideal_component_sum_le_growth F I hhom N

theorem sparse_furtherQuotient_growth_quadratic_lower (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (I : TwoSidedIdeal (WordAlgebra F))
    (hEI : allCutTwoSidedIdeal F (sparseDualData F Λ hΛ)
      (sparseDualData_primalCoherent F Λ hΛ) ≤ I)
    (hhom : WordIdealHomogeneous F I) (htail : NoWordTail F I) (N : ℕ) :
    N * (N + 3) ≤ 2 * idealPositiveDegreeGrowth F I N := by
  rw [idealPositiveDegreeGrowth_eq_component_sum F I hhom N,
    ← twice_sum_linear_degrees]
  apply Nat.mul_le_mul_left
  apply Finset.sum_le_sum
  intro m _
  exact sparse_furtherQuotient_degree_finrank_lower F Λ hΛ I hEI htail (m + 1)

#print axioms CriticalGK2.Actual.idealPositiveDegreeGrowth_eq_component_sum
#print axioms CriticalGK2.Actual.sparse_furtherQuotient_growth_quadratic_lower

end

end CriticalGK2.Actual
