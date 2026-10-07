import CriticalGK2.CutDuality
import CriticalGK2.DyadicDegreeCast
import CriticalGK2.WordSurvival

/-!
# Actual completion annihilators are whole-exterior contraction supports

An arbitrary functional on the entire external dual homogeneous space is
represented by the finite-dimensional evaluation equivalence.  The contraction
is the actual dual of multiplication by its representing primal vector.  The
coannihilator of the span of all such contractions of the actual W at the root
is proved to be the actual R/L completion.  Finite double-annihilator duality
then identifies the completion annihilator with that complete contraction span.

The hypotheses specify the family W and finite-dimensional word spaces.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

theorem completionRootDegree (n : ℕ) :
    n + (2 ^ strictDyadicRoot n - n) = 2 ^ strictDyadicRoot n :=
  Nat.add_sub_of_le (degree_lt_strictDyadicPower n).le

theorem completionRootDegreeLeft (n : ℕ) :
    (2 ^ strictDyadicRoot n - n) + n = 2 ^ strictDyadicRoot n := by
  rw [Nat.add_comm]
  exact completionRootDegree n

/-- Actual right multiplication, with its codomain at the literal dyadic root. -/
def rightCompletionTestMap (n : ℕ)
    (y : homogeneous F (2 ^ strictDyadicRoot n - n)) :
    homogeneous F n →ₗ[F] homogeneous F (2 ^ strictDyadicRoot n) where
  toFun x := ⟨x.val * y.val, by
    have hxy := homogeneous_mul F x.property y.property
    simpa only [completionRootDegree] using hxy⟩
  map_add' x x' := Subtype.ext (add_mul x.val x'.val y.val)
  map_smul' c x := Subtype.ext (smul_mul_assoc c x.val y.val)

/-- Actual left multiplication at the literal dyadic root. -/
def leftCompletionTestMap (n : ℕ)
    (y : homogeneous F (2 ^ strictDyadicRoot n - n)) :
    homogeneous F n →ₗ[F] homogeneous F (2 ^ strictDyadicRoot n) where
  toFun x := ⟨y.val * x.val, by
    have hyx := homogeneous_mul F y.property x.property
    simpa only [completionRootDegreeLeft] using hyx⟩
  map_add' x x' := Subtype.ext (mul_add y.val x.val x'.val)
  map_smul' c x := Subtype.ext (mul_smul_comm c y.val x.val)

/-- Retain the prefix, contracting any functional on the complete external dual. -/
def actualRootPrefixContraction (n : ℕ)
    (η : Module.Dual F (HomogeneousDual F (2 ^ strictDyadicRoot n - n))) :
    HomogeneousDual F (2 ^ strictDyadicRoot n) →ₗ[F] HomogeneousDual F n :=
  (rightCompletionTestMap F n
    ((Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n))).symm η)).dualMap

/-- Retain the suffix, contracting any functional on the complete external dual. -/
def actualRootSuffixContraction (n : ℕ)
    (η : Module.Dual F (HomogeneousDual F (2 ^ strictDyadicRoot n - n))) :
    HomogeneousDual F (2 ^ strictDyadicRoot n) →ₗ[F] HomogeneousDual F n :=
  (leftCompletionTestMap F n
    ((Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n))).symm η)).dualMap

@[simp]
theorem actualRootPrefixContraction_eval (n : ℕ)
    (y : homogeneous F (2 ^ strictDyadicRoot n - n))
    (φ : HomogeneousDual F (2 ^ strictDyadicRoot n)) (x : homogeneous F n) :
    actualRootPrefixContraction F n
      (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n)) y) φ x =
      φ (rightCompletionTestMap F n y x) := by
  change φ (rightCompletionTestMap F n
    ((Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n))).symm
      (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n)) y)) x) = _
  rw [LinearEquiv.symm_apply_apply]

@[simp]
theorem actualRootSuffixContraction_eval (n : ℕ)
    (y : homogeneous F (2 ^ strictDyadicRoot n - n))
    (φ : HomogeneousDual F (2 ^ strictDyadicRoot n)) (x : homogeneous F n) :
    actualRootSuffixContraction F n
      (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n)) y) φ x =
      φ (leftCompletionTestMap F n y x) := by
  change φ (leftCompletionTestMap F n
    ((Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n))).symm
      (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n)) y)) x) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Span of all whole-exterior prefix contractions of the actual W at the root. -/
def actualRootPrefixContractionSupport (W : DyadicDualData F) (n : ℕ) :
    Submodule F (HomogeneousDual F n) :=
  ⨆ η : Module.Dual F (HomogeneousDual F (2 ^ strictDyadicRoot n - n)),
    (W (strictDyadicRoot n)).map (actualRootPrefixContraction F n η)

/-- Span of all whole-exterior suffix contractions of the actual W at the root. -/
def actualRootSuffixContractionSupport (W : DyadicDualData F) (n : ℕ) :
    Submodule F (HomogeneousDual F n) :=
  ⨆ η : Module.Dual F (HomogeneousDual F (2 ^ strictDyadicRoot n - n)),
    (W (strictDyadicRoot n)).map (actualRootSuffixContraction F n η)

/-- Complete prefix contraction span has exactly the actual R_n as coannihilator. -/
theorem actualRootPrefixContractionSupport_dualCoannihilator
    (W : DyadicDualData F) (n : ℕ) (hn : n ≠ 0) :
    (actualRootPrefixContractionSupport F W n).dualCoannihilator =
      homogeneousRightCompletion F W n := by
  rw [actualRootPrefixContractionSupport, Submodule.dualCoannihilator_iSup_eq]
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    change x.val ∈ rightCompletion F W n
    rw [rightCompletion, if_neg hn]
    refine ⟨x.property, ?_⟩
    apply (Submodule.mem_iInf _).mpr
    intro y
    have hy := (Submodule.mem_iInf _).mp hx
      (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n)) y)
    have htest : rightCompletionTestMap F n y x ∈
        dyadicAnnihilator F W (strictDyadicRoot n) := by
      rw [mem_dyadicAnnihilator_iff]
      intro φ hφ
      have himage : actualRootPrefixContraction F n
          (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n)) y) φ ∈
          (W (strictDyadicRoot n)).map
            (actualRootPrefixContraction F n
              (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n)) y)) :=
        Submodule.mem_map.mpr ⟨φ, hφ, rfl⟩
      have hz := (Submodule.mem_dualCoannihilator x).mp hy _ himage
      simpa only [actualRootPrefixContraction_eval] using hz
    exact Submodule.mem_map.mpr ⟨rightCompletionTestMap F n y x, htest, rfl⟩
  · intro hx
    change x.val ∈ rightCompletion F W n at hx
    rw [rightCompletion, if_neg hn] at hx
    apply (Submodule.mem_iInf _).mpr
    intro η
    rw [Submodule.mem_dualCoannihilator]
    intro θ hθ
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.mp hθ
    let y := (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n))).symm η
    have hxy := (Submodule.mem_iInf _).mp hx.2 y
    have htest : rightCompletionTestMap F n y x ∈
        dyadicAnnihilator F W (strictDyadicRoot n) :=
      (homogeneous_mem_ambientAnnihilator_iff F W (strictDyadicRoot n)
        (rightCompletionTestMap F n y x)).mp hxy
    exact (mem_dyadicAnnihilator_iff F W (strictDyadicRoot n)
      (rightCompletionTestMap F n y x)).mp htest φ hφ

/-- Complete suffix contraction span has exactly the actual L_n as coannihilator. -/
theorem actualRootSuffixContractionSupport_dualCoannihilator
    (W : DyadicDualData F) (n : ℕ) (hn : n ≠ 0) :
    (actualRootSuffixContractionSupport F W n).dualCoannihilator =
      homogeneousLeftCompletion F W n := by
  rw [actualRootSuffixContractionSupport, Submodule.dualCoannihilator_iSup_eq]
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    change x.val ∈ leftCompletion F W n
    rw [leftCompletion, if_neg hn]
    refine ⟨x.property, ?_⟩
    apply (Submodule.mem_iInf _).mpr
    intro y
    have hy := (Submodule.mem_iInf _).mp hx
      (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n)) y)
    have htest : leftCompletionTestMap F n y x ∈
        dyadicAnnihilator F W (strictDyadicRoot n) := by
      rw [mem_dyadicAnnihilator_iff]
      intro φ hφ
      have himage : actualRootSuffixContraction F n
          (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n)) y) φ ∈
          (W (strictDyadicRoot n)).map
            (actualRootSuffixContraction F n
              (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n)) y)) :=
        Submodule.mem_map.mpr ⟨φ, hφ, rfl⟩
      have hz := (Submodule.mem_dualCoannihilator x).mp hy _ himage
      simpa only [actualRootSuffixContraction_eval] using hz
    exact Submodule.mem_map.mpr ⟨leftCompletionTestMap F n y x, htest, rfl⟩
  · intro hx
    change x.val ∈ leftCompletion F W n at hx
    rw [leftCompletion, if_neg hn] at hx
    apply (Submodule.mem_iInf _).mpr
    intro η
    rw [Submodule.mem_dualCoannihilator]
    intro θ hθ
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.mp hθ
    let y := (Module.evalEquiv F (homogeneous F (2 ^ strictDyadicRoot n - n))).symm η
    have hyx := (Submodule.mem_iInf _).mp hx.2 y
    have htest : leftCompletionTestMap F n y x ∈
        dyadicAnnihilator F W (strictDyadicRoot n) :=
      (homogeneous_mem_ambientAnnihilator_iff F W (strictDyadicRoot n)
        (leftCompletionTestMap F n y x)).mp hyx
    exact (mem_dyadicAnnihilator_iff F W (strictDyadicRoot n)
      (leftCompletionTestMap F n y x)).mp htest φ hφ

/-- Actual right completion annihilator equals the whole prefix contraction span. -/
theorem homogeneousRightCompletion_dualAnnihilator
    (W : DyadicDualData F) (n : ℕ) (hn : n ≠ 0) :
    (homogeneousRightCompletion F W n).dualAnnihilator =
      actualRootPrefixContractionSupport F W n := by
  classical
  letI : FiniteDimensional F (HomogeneousDual F n) :=
    (homogeneousWordBasis F n).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (actualRootPrefixContractionSupport F W n) :=
    FiniteDimensional.of_injective
      (actualRootPrefixContractionSupport F W n).subtype Subtype.val_injective
  rw [← actualRootPrefixContractionSupport_dualCoannihilator F W n hn]
  exact Subspace.dualCoannihilator_dualAnnihilator_eq

/-- Actual left completion annihilator equals the whole suffix contraction span. -/
theorem homogeneousLeftCompletion_dualAnnihilator
    (W : DyadicDualData F) (n : ℕ) (hn : n ≠ 0) :
    (homogeneousLeftCompletion F W n).dualAnnihilator =
      actualRootSuffixContractionSupport F W n := by
  classical
  letI : FiniteDimensional F (HomogeneousDual F n) :=
    (homogeneousWordBasis F n).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (actualRootSuffixContractionSupport F W n) :=
    FiniteDimensional.of_injective
      (actualRootSuffixContractionSupport F W n).subtype Subtype.val_injective
  rw [← actualRootSuffixContractionSupport_dualCoannihilator F W n hn]
  exact Subspace.dualCoannihilator_dualAnnihilator_eq

end

end CriticalGK2.Actual
