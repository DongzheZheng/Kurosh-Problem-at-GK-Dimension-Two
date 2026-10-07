import CriticalGK2.DualWordBridge
import CriticalGK2.ActualBlockPowers

/-!
# The genuine local PI in the actual homogeneous dual word space

The polynomial PI, arbitrary linear-combination stem, reset prefix and repeated
original-block containment are transported through the proved coefficient
identification. The matrix evaluation relation follows by applying the
inverse identification.
-/

namespace CriticalGK2.Actual

open TensorProduct

variable (F : Type*) [Field F]

/-- Actual physical degree of the local PI polynomial. -/
def localPIDegree (n k : ℕ) (u : FreeMonoid Bool) : ℕ :=
  ((k * k + 1) * (k * k + 1) + u.length) * (n + 1)

/-- The arbitrary-stem local PI is in its actual homogeneous component. -/
theorem localPIBlock_mem_homogeneous (n : ℕ) (t : CriticalGK2.StemWord n → F)
    (k : ℕ) (u : FreeMonoid Bool) :
    CriticalGK2.localPIBlock F n t k u ∈ homogeneous F (localPIDegree n k u) :=
  (wordHomogeneous_iff_mem_homogeneous F _ _).mp
    (CriticalGK2.localPIBlock_homogeneous F n t k u)

/-- The actual homogeneous-dual PI used in the dyadic construction. -/
noncomputable def actualLocalPI (n : ℕ) (t : CriticalGK2.StemWord n → F)
    (k : ℕ) (u : FreeMonoid Bool) : HomogeneousDual F (localPIDegree n k u) :=
  ambientToDual F (localPIDegree n k u) (CriticalGK2.localPIBlock F n t k u)

/-- The actual dual PI is nonzero for every nonzero arbitrary stem. -/
theorem actualLocalPI_ne_zero (n : ℕ) (t : CriticalGK2.StemWord n → F) (ht : t ≠ 0)
    (k : ℕ) (u : FreeMonoid Bool) : actualLocalPI F n t k u ≠ 0 :=
  ambientToDual_ne_zero F _ _ (localPIBlock_mem_homogeneous F n t k u)
    (CriticalGK2.localPIBlock_ne_zero F n t ht k u)

/-- Reconstructing the actual dual PI returns the exact polynomial originally built. -/
theorem dualToAmbient_actualLocalPI (n : ℕ) (t : CriticalGK2.StemWord n → F)
    (k : ℕ) (u : FreeMonoid Bool) :
    dualToAmbient F (localPIDegree n k u) (actualLocalPI F n t k u) =
      CriticalGK2.localPIBlock F n t k u :=
  dualToAmbient_ambientToDual F _ _ (localPIBlock_mem_homogeneous F n t k u)

/-- The real actual-dual evaluation vanishes over every commutative coefficient algebra. -/
theorem actualLocalPI_matrix_evaluation_eq_zero (C : Type*) [CommRing C] [Algebra F C]
    (n : ℕ) (t : CriticalGK2.StemWord n → F) (k : ℕ) (u : FreeMonoid Bool)
    (v : Bool → Matrix (Fin k) (Fin k) C) :
    actualDualMatrixEvaluation F C k (localPIDegree n k u) v (actualLocalPI F n t k u) = 0 := by
  simp only [actualDualMatrixEvaluation, LinearMap.comp_apply]
  rw [dualToAmbient_actualLocalPI]
  exact CriticalGK2.localPIBlock_evaluation_eq_zero F C n t k u v

/-- The actual dual PI lies in the actual image of the original repeated-block space. -/
theorem actualLocalPI_mem_repeatedBlockSpace (n : ℕ) (t : CriticalGK2.StemWord n → F)
    (k : ℕ) (u : FreeMonoid Bool) :
    actualLocalPI F n t k u ∈ dualCoefficientSpace F (localPIDegree n k u)
      (CriticalGK2.repeatedBlockSpace F n t ((k * k + 1) * (k * k + 1) + u.length)) := by
  exact ⟨CriticalGK2.localPIBlock F n t k u,
    CriticalGK2.localPIBlock_mem_repeatedBlockSpace F n t k u, rfl⟩

/-- The actual original two-block space raised to a genuine multiplication power,
then transported through its complete coefficient identification. -/
noncomputable def actualBlockPowerSpace (n : ℕ) (t : CriticalGK2.StemWord n → F)
    (m : ℕ) : Submodule F (HomogeneousDual F (m * (n + 1))) :=
  dualCoefficientSpace F (m * (n + 1)) (blockPower F (stemSpace F n t) m)

/-- The actual dual PI lies in the proved original block-power configuration. -/
theorem actualLocalPI_mem_actualBlockPowerSpace (n : ℕ)
    (t : CriticalGK2.StemWord n → F) (k : ℕ) (u : FreeMonoid Bool) :
    actualLocalPI F n t k u ∈
      actualBlockPowerSpace F n t ((k * k + 1) * (k * k + 1) + u.length) :=
  ⟨CriticalGK2.localPIBlock F n t k u, localPIBlock_mem_blockPower F n t k u, rfl⟩

/-- A nonzero actual homogeneous primal space remains nonzero after coefficient dualization. -/
theorem dualCoefficientSpace_ne_bot (n : ℕ) (S : Submodule F (WordAlgebra F))
    (hS : S ≤ homogeneous F n) (hne : S ≠ ⊥) : dualCoefficientSpace F n S ≠ ⊥ := by
  obtain ⟨P, hP, hPne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  intro hzero
  have hm : ambientToDual F n P ∈ dualCoefficientSpace F n S := ⟨P, hP, rfl⟩
  rw [hzero] at hm
  exact ambientToDual_ne_zero F n P (hS hP) hPne ((Submodule.mem_bot F).mp hm)

/-- All original block-power configurations are actually nonzero for a nonzero stem. -/
theorem actualBlockPowerSpace_ne_bot (n : ℕ)
    (t : CriticalGK2.StemWord n → F) (ht : t ≠ 0) (m : ℕ) :
    actualBlockPowerSpace F n t m ≠ ⊥ := by
  obtain ⟨P, hP, hPne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (stemSpace_ne_bot F n t ht)
  exact dualCoefficientSpace_ne_bot F _ _
    (blockPower_le_homogeneous F _ (n + 1) (stemSpace_le_homogeneous F n t) m)
    (blockPower_ne_bot F _ P hP hPne m)

/-- Splitting a genuine primal block power gives the actual dual tensor-product
containment needed at every dyadic intermediate layer.  Degree equality is
written explicitly as `a*q+b*q` for use with proved degree casts. -/
theorem actualBlockPowerSpace_tensor_split (n : ℕ)
    (t : CriticalGK2.StemWord n → F) (a b : ℕ) :
    dualCoefficientSpace F (a * (n + 1) + b * (n + 1))
        (blockPower F (stemSpace F n t) (a + b)) ≤
      actualDualTensorProduct F (a * (n + 1)) (b * (n + 1))
        (actualBlockPowerSpace F n t a) (actualBlockPowerSpace F n t b) := by
  rw [← productSpan_blockPower]
  exact dualCoefficientSpace_productSpan_le F _ _ _ _
    (blockPower_le_homogeneous F _ (n + 1) (stemSpace_le_homogeneous F n t) a)
    (blockPower_le_homogeneous F _ (n + 1) (stemSpace_le_homogeneous F n t) b)

/-- The original arbitrary stem as an actual dual tensor coefficient. -/
noncomputable def actualStem (n : ℕ) (t : CriticalGK2.StemWord n → F) : HomogeneousDual F n :=
  ambientToDual F n (CriticalGK2.stemPolynomial F n t)

/-- The arbitrary old stem is a nonzero actual dual element. -/
theorem actualStem_ne_zero (n : ℕ) (t : CriticalGK2.StemWord n → F) (ht : t ≠ 0) :
    actualStem F n t ≠ 0 :=
  ambientToDual_ne_zero F _ _
    ((wordHomogeneous_iff_mem_homogeneous F _ _).mp (CriticalGK2.stemPolynomial_homogeneous F n t))
    (CriticalGK2.stemPolynomial_ne_zero F n t ht)

/-- A reset common prefix, in the actual homogeneous-dual space. -/
noncomputable def actualResetStem (n : ℕ) (t : CriticalGK2.StemWord n → F)
    (k : ℕ) (u : FreeMonoid Bool) : HomogeneousDual F (localPIDegree n k u + n) :=
  ambientToDual F _ (CriticalGK2.localResetStem F n t k u)

/-- The reset prefix is nonzero. -/
theorem actualResetStem_ne_zero (n : ℕ) (t : CriticalGK2.StemWord n → F) (ht : t ≠ 0)
    (k : ℕ) (u : FreeMonoid Bool) : actualResetStem F n t k u ≠ 0 :=
  ambientToDual_ne_zero F _ _
    ((wordHomogeneous_iff_mem_homogeneous F _ _).mp (CriticalGK2.localResetStem_homogeneous F n t k u))
    (CriticalGK2.localResetStem_ne_zero F n t ht k u)

/-- The reset stem is the genuine actual dual concatenation of the PI and old stem. -/
theorem actualResetStem_eq_tensorConcat (n : ℕ) (t : CriticalGK2.StemWord n → F)
    (k : ℕ) (u : FreeMonoid Bool) :
    actualResetStem F n t k u = homogeneousDualTensorConcat F (localPIDegree n k u) n
      (actualLocalPI F n t k u ⊗ₜ[F] actualStem F n t) := by
  exact ambientToDual_mul F _ _ _ _ (localPIBlock_mem_homogeneous F n t k u)
    ((wordHomogeneous_iff_mem_homogeneous F _ _).mp (CriticalGK2.stemPolynomial_homogeneous F n t))

end CriticalGK2.Actual
