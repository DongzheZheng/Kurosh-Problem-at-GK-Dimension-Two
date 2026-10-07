import CriticalGK2.LocalContainment

/-!
# Physical common-prefix polynomials and reset stems

This file identifies the explicit block substitution with the common-prefix
formula `t * x`, `t * y` in the actual two-letter free algebra.  The new reset
stem `g * t` is nonzero and homogeneous.  All statements are in the ambient free
algebra, before any quotient is constructed.
-/

namespace CriticalGK2

open scoped BigOperators

/-- The actual homogeneous polynomial represented by a stem coefficient vector. -/
noncomputable def stemPolynomial (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) : BinaryFreeAlgebra F :=
  ∑ a : StemWord n, t a • MonoidAlgebra.single (FreeMonoid.ofList (List.ofFn a)) 1

/-- Fixed-length basis words retain exactly their original stem coefficients. -/
theorem stemPolynomial_coefficient (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (a₀ : StemWord n) :
    stemPolynomial F n t (FreeMonoid.ofList (List.ofFn a₀)) = t a₀ := by
  classical
  rw [stemPolynomial, binaryFinsetSum_apply]
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ ha
    have hword : FreeMonoid.ofList (List.ofFn a) ≠ FreeMonoid.ofList (List.ofFn a₀) := by
      intro heq
      exact ha (List.ofFn_injective (congrArg FreeMonoid.toList heq))
    change t a • (MonoidAlgebra.single (FreeMonoid.ofList (List.ofFn a)) (1 : F)
      (FreeMonoid.ofList (List.ofFn a₀))) = 0
    rw [MonoidAlgebra.single_apply, if_neg hword, smul_zero]
  · simp

/-- A nonzero coefficient vector is a nonzero actual prefix polynomial. -/
theorem stemPolynomial_ne_zero (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (ht : t ≠ 0) : stemPolynomial F n t ≠ 0 := by
  classical
  have hex : ∃ a₀, t a₀ ≠ 0 := by
    by_contra! h
    exact ht (funext h)
  obtain ⟨a₀, ha₀⟩ := hex
  intro h
  have hc := stemPolynomial_coefficient F n t a₀
  rw [h] at hc
  exact ha₀ (by simpa using hc.symm)

/-- The prefix polynomial has its prescribed physical degree. -/
theorem stemPolynomial_homogeneous (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) : WordHomogeneous n (stemPolynomial F n t) := by
  apply wordHomogeneous_sum
  intro a _
  apply wordHomogeneous_smul
  simpa only [FreeMonoid.length, FreeMonoid.toList_ofList, List.length_ofFn] using
    (wordHomogeneous_single (FreeMonoid.ofList (List.ofFn a)) (1 : F))

/-- The block injection is the actual common-prefix substitution. -/
theorem stemEmbedding_binaryLetter_eq_prefix_mul (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (b : Bool) :
    stemEmbedding F n t (binaryLetter F b) = stemPolynomial F n t * binaryLetter F b := by
  classical
  rw [stemEmbedding_binaryLetter, stemPolynomial, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_mul_assoc]
  congr 1
  simp only [binaryLetter, MonoidAlgebra.single_mul_single, mul_one]
  rfl

/-- Every actual word of degree `n` is represented by one fixed-length tuple. -/
theorem exists_stemWord_of_length (n : ℕ) (w : FreeMonoid Bool) (hw : w.length = n) :
    ∃ a : StemWord n, FreeMonoid.ofList (List.ofFn a) = w := by
  subst n
  refine ⟨w.toList.get, ?_⟩
  exact (congrArg FreeMonoid.ofList (List.ofFn_get w.toList)).trans
    (FreeMonoid.ofList_toList w)

/-- Homogeneous polynomials can be reconstructed from their full fixed-length
coefficient vector.  This allows a reset prefix to become the next actual stem. -/
theorem stemPolynomial_of_coefficients (F : Type*) [Field F] (n : ℕ)
    (P : BinaryFreeAlgebra F) (hP : WordHomogeneous n P) :
    stemPolynomial F n (fun a => P (FreeMonoid.ofList (List.ofFn a))) = P := by
  classical
  ext w
  by_cases hw : w.length = n
  · obtain ⟨a, rfl⟩ := exists_stemWord_of_length n w hw
    exact stemPolynomial_coefficient F n _ a
  · have hl : stemPolynomial F n (fun a => P (FreeMonoid.ofList (List.ofFn a))) w = 0 := by
      by_contra hne
      exact hw (stemPolynomial_homogeneous F n _ w hne)
    have hr : P w = 0 := by
      by_contra hne
      exact hw (hP w hne)
    rw [hl, hr]

/-- A nonzero homogeneous polynomial has a nonzero fixed-length coefficient vector. -/
theorem homogeneous_coefficients_ne_zero (F : Type*) [Field F] (n : ℕ)
    (P : BinaryFreeAlgebra F) (hP : WordHomogeneous n P) (hne : P ≠ 0) :
    (fun a : StemWord n => P (FreeMonoid.ofList (List.ofFn a))) ≠ 0 := by
  intro h
  apply hne
  rw [← stemPolynomial_of_coefficients F n P hP, h]
  simp [stemPolynomial]

/-- The next common prefix produced by the local operation, in the ambient algebra. -/
noncomputable def localResetStem (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool) : BinaryFreeAlgebra F :=
  localPIBlock F n t k u * stemPolynomial F n t

/-- The local reset cannot kill the common prefix. -/
theorem localResetStem_ne_zero (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (ht : t ≠ 0) (k : ℕ) (u : FreeMonoid Bool) :
    localResetStem F n t k u ≠ 0 := by
  exact mul_ne_zero (localPIBlock_ne_zero F n t ht k u) (stemPolynomial_ne_zero F n t ht)

/-- The reset prefix remains homogeneous at the expected physical degree. -/
theorem localResetStem_homogeneous (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool) :
    WordHomogeneous
      ((((k * k + 1) * (k * k + 1) + u.length) * (n + 1)) + n)
      (localResetStem F n t k u) :=
  wordHomogeneous_mul (localPIBlock_homogeneous F n t k u) (stemPolynomial_homogeneous F n t)

/-- The physical degree of the reset common prefix. -/
def localResetDegree (n k : ℕ) (u : FreeMonoid Bool) : ℕ :=
  (((k * k + 1) * (k * k + 1) + u.length) * (n + 1)) + n

/-- Full coefficient vector of the reset prefix, ready as input to the next operation. -/
noncomputable def localResetCoefficients (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool) :
    StemWord (localResetDegree n k u) → F :=
  fun a => localResetStem F n t k u (FreeMonoid.ofList (List.ofFn a))

/-- Exact reset readback: the next coefficient vector represents the actual product `g*t`. -/
theorem stemPolynomial_localResetCoefficients (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool) :
    stemPolynomial F (localResetDegree n k u) (localResetCoefficients F n t k u) =
      localResetStem F n t k u :=
  stemPolynomial_of_coefficients F _ _ (localResetStem_homogeneous F n t k u)

/-- The next stem vector is nonzero. -/
theorem localResetCoefficients_ne_zero (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (ht : t ≠ 0) (k : ℕ) (u : FreeMonoid Bool) :
    localResetCoefficients F n t k u ≠ 0 :=
  homogeneous_coefficients_ne_zero F _ _ (localResetStem_homogeneous F n t k u)
    (localResetStem_ne_zero F n t ht k u)

/-- The new two generators share exactly the actual reset prefix. -/
theorem localPIBlock_mul_stemBlock_eq_reset_prefix (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool) (b : Bool) :
    localPIBlock F n t k u * stemEmbedding F n t (binaryLetter F b) =
      localResetStem F n t k u * binaryLetter F b := by
  rw [stemEmbedding_binaryLetter_eq_prefix_mul, ← mul_assoc]
  rfl

end CriticalGK2
