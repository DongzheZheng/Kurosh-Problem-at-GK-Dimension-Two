import CriticalGK2.ActualBlockPowers

/-!
# Concrete common-prefix waiting and reset steps

Both outputs are full coefficient functions of actual homogeneous polynomials.
Their nonzeroness and block-space coherence are derived from the actual
operations. The reset space is killed by every matrix algebra evaluation of
the specified order.
-/

namespace CriticalGK2.Actual

noncomputable section

open CriticalGK2

variable (F : Type*) [Field F]

theorem binaryLetter_ne_zero (b : Bool) : binaryLetter F b ≠ 0 := by
  exact MonoidAlgebra.single_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)

def waitingStem (n : ℕ) (t : StemWord n → F) : WordAlgebra F :=
  (stemPolynomial F n t * binaryLetter F false) * stemPolynomial F n t

theorem waitingStem_ne_zero (n : ℕ) (t : StemWord n → F) (ht : t ≠ 0) :
    waitingStem F n t ≠ 0 :=
  mul_ne_zero (mul_ne_zero (stemPolynomial_ne_zero F n t ht)
    (binaryLetter_ne_zero F false)) (stemPolynomial_ne_zero F n t ht)

theorem waitingStem_homogeneous (n : ℕ) (t : StemWord n → F) :
    WordHomogeneous (2 * n + 1) (waitingStem F n t) := by
  have hb : WordHomogeneous 1 (binaryLetter F false) := by
    simpa only [binaryLetter, FreeMonoid.length_of] using
      (wordHomogeneous_single (FreeMonoid.of false) (1 : F))
  have h := wordHomogeneous_mul
    (wordHomogeneous_mul (stemPolynomial_homogeneous F n t) hb)
    (stemPolynomial_homogeneous F n t)
  convert h using 1 <;> omega

def waitingCoefficients (n : ℕ) (t : StemWord n → F) : StemWord (2 * n + 1) → F :=
  fun a => waitingStem F n t (FreeMonoid.ofList (List.ofFn a))

theorem stemPolynomial_waitingCoefficients (n : ℕ) (t : StemWord n → F) :
    stemPolynomial F (2 * n + 1) (waitingCoefficients F n t) = waitingStem F n t :=
  stemPolynomial_of_coefficients F _ _ (waitingStem_homogeneous F n t)

theorem waitingCoefficients_ne_zero (n : ℕ) (t : StemWord n → F) (ht : t ≠ 0) :
    waitingCoefficients F n t ≠ 0 :=
  homogeneous_coefficients_ne_zero F _ _ (waitingStem_homogeneous F n t)
    (waitingStem_ne_zero F n t ht)

theorem waitingSpace_le_product (n : ℕ) (t : StemWord n → F) :
    stemSpace F (2 * n + 1) (waitingCoefficients F n t) ≤
      productSpan F (stemSpace F n t) (stemSpace F n t) := by
  apply Submodule.span_le.mpr
  rintro x ⟨b, rfl⟩
  change stemEmbedding F (2 * n + 1) (waitingCoefficients F n t)
    (binaryLetter F b) ∈ _
  rw [stemEmbedding_binaryLetter_eq_prefix_mul, stemPolynomial_waitingCoefficients]
  have hx := mul_mem_productSpan F (physicalBlock_mem_stemSpace F n t false)
    (physicalBlock_mem_stemSpace F n t b)
  simpa only [stemEmbedding_binaryLetter_eq_prefix_mul, waitingStem, mul_assoc] using hx

theorem resetSpace_le_blockPower (n : ℕ) (t : StemWord n → F)
    (k : ℕ) (u : FreeMonoid Bool) :
    stemSpace F (localResetDegree n k u) (localResetCoefficients F n t k u) ≤
      blockPower F (stemSpace F n t)
        (((k * k + 1) * (k * k + 1) + u.length) + 1) := by
  apply Submodule.span_le.mpr
  rintro x ⟨b, rfl⟩
  change stemEmbedding F (localResetDegree n k u) (localResetCoefficients F n t k u)
    (binaryLetter F b) ∈ _
  rw [stemEmbedding_binaryLetter_eq_prefix_mul, stemPolynomial_localResetCoefficients]
  rw [← localPIBlock_mul_stemBlock_eq_reset_prefix]
  exact mul_mem_productSpan F (localPIBlock_mem_blockPower F n t k u)
    (physicalBlock_mem_stemSpace F n t b)

theorem localPIBlock_algHom_eq_zero (C : Type*) [CommRing C] [Algebra F C]
    (n : ℕ) (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool)
    (f : WordAlgebra F →ₐ[F] Matrix (Fin k) (Fin k) C) :
    f (localPIBlock F n t k u) = 0 := by
  have hf : f = binaryEvaluation F (Matrix (Fin k) (Fin k) C)
      (fun b => f (binaryLetter F b)) := by
    apply freeMonoidAlgebra_hom_ext_letters
    intro b
    simp [binaryEvaluation, binaryLetter]
  rw [hf]
  exact localPIBlock_evaluation_eq_zero F C n t k u _

theorem resetSpace_le_matrix_kernel (C : Type*) [CommRing C] [Algebra F C]
    (n : ℕ) (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool)
    (f : WordAlgebra F →ₐ[F] Matrix (Fin k) (Fin k) C) :
    stemSpace F (localResetDegree n k u) (localResetCoefficients F n t k u) ≤
      LinearMap.ker f.toLinearMap := by
  apply Submodule.span_le.mpr
  rintro x ⟨b, rfl⟩
  change f (stemEmbedding F (localResetDegree n k u)
    (localResetCoefficients F n t k u) (binaryLetter F b)) = 0
  rw [stemEmbedding_binaryLetter_eq_prefix_mul, stemPolynomial_localResetCoefficients]
  rw [← localPIBlock_mul_stemBlock_eq_reset_prefix, map_mul,
    localPIBlock_algHom_eq_zero, zero_mul]

theorem waiting_dyadic_degree (h : ℕ) :
    2 * (2 ^ h - 1) + 1 = 2 ^ (h + 1) - 1 := by
  have hp : 0 < (2 : ℕ) ^ h := pow_pos (by norm_num) _
  rw [pow_succ]
  omega

end

end CriticalGK2.Actual
