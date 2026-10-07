import CriticalGK2.PolynomialStages
import CriticalGK2.DyadicRoots

/-!
# Actual dyadic prefix states and their two constructive transitions

`PrefixState` stores a literal polynomial, its degree and its nonzeroness.
Its constructors prove these facts. The local PI cost is the degree of
the one-hot code used in the construction.
-/

namespace CriticalGK2.Actual

noncomputable section

open CriticalGK2

variable (F : Type*) [Field F]

def prefixSpace (P : WordAlgebra F) : Submodule F (WordAlgebra F) :=
  Submodule.span F (Set.range fun b : Bool => P * binaryLetter F b)

theorem prefixGenerator_mem (P : WordAlgebra F) (b : Bool) :
    P * binaryLetter F b ∈ prefixSpace F P := Submodule.subset_span ⟨b, rfl⟩

theorem stemSpace_eq_prefixSpace (n : ℕ) (t : StemWord n → F) :
    stemSpace F n t = prefixSpace F (stemPolynomial F n t) := by
  simp only [stemSpace, prefixSpace, stemEmbedding_binaryLetter_eq_prefix_mul]

theorem prefixSpace_le_homogeneous (P : WordAlgebra F) (n : ℕ)
    (hP : WordHomogeneous n P) : prefixSpace F P ≤ homogeneous F (n + 1) := by
  apply Submodule.span_le.mpr
  rintro x ⟨b, rfl⟩
  have hb : WordHomogeneous 1 (binaryLetter F b) := by
    simpa only [binaryLetter, FreeMonoid.length_of] using
      wordHomogeneous_single (FreeMonoid.of b) (1 : F)
  exact wordHomogeneous_mem_homogeneous F _ _ (wordHomogeneous_mul hP hb)

theorem prefixSpace_ne_bot (P : WordAlgebra F) (hP : P ≠ 0) :
    prefixSpace F P ≠ ⊥ := by
  intro h
  have hx := prefixGenerator_mem F P false
  rw [h] at hx
  exact (mul_ne_zero hP (binaryLetter_ne_zero F false)) ((Submodule.mem_bot F).mp hx)

structure PrefixState where
  height : ℕ
  polynomial : WordAlgebra F
  homogeneous : WordHomogeneous (2 ^ height - 1) polynomial
  nonzero : polynomial ≠ 0

def prefixCoefficients (P : PrefixState F) : StemWord (2 ^ P.height - 1) → F :=
  fun a => P.polynomial (FreeMonoid.ofList (List.ofFn a))

theorem prefixCoefficients_nonzero (P : PrefixState F) :
    prefixCoefficients F P ≠ 0 :=
  homogeneous_coefficients_ne_zero F _ _ P.homogeneous P.nonzero

theorem prefixCoefficients_readback (P : PrefixState F) :
    stemPolynomial F (2 ^ P.height - 1) (prefixCoefficients F P) = P.polynomial :=
  stemPolynomial_of_coefficients F _ _ P.homogeneous

def initialPrefix : PrefixState F where
  height := 0
  polynomial := 1
  homogeneous := by
    have h := wordHomogeneous_single (1 : FreeMonoid Bool) (1 : F)
    simpa [MonoidAlgebra.one_def] using h
  nonzero := one_ne_zero

def waitPrefix (P : PrefixState F) : PrefixState F where
  height := P.height + 1
  polynomial := (P.polynomial * binaryLetter F false) * P.polynomial
  homogeneous := by
    have h := waitingStem_homogeneous F (2 ^ P.height - 1) (prefixCoefficients F P)
    rw [waitingStem, prefixCoefficients_readback, waiting_dyadic_degree] at h
    exact h
  nonzero := mul_ne_zero (mul_ne_zero P.nonzero (binaryLetter_ne_zero F false)) P.nonzero

@[simp] theorem waitPrefix_height (P : PrefixState F) :
    (waitPrefix F P).height = P.height + 1 := rfl

theorem waitPrefix_space_coherent (P : PrefixState F) :
    prefixSpace F (waitPrefix F P).polynomial ≤
      productSpan F (prefixSpace F P.polynomial) (prefixSpace F P.polynomial) := by
  apply Submodule.span_le.mpr
  rintro x ⟨b, rfl⟩
  have hx := mul_mem_productSpan F (prefixGenerator_mem F P.polynomial false)
    (prefixGenerator_mem F P.polynomial b)
  simpa only [waitPrefix, mul_assoc] using hx

def operationDegree (k : ℕ) : ℕ := (k * k + 1) * (k * k + 1)
def operationHeight (k : ℕ) : ℕ := strictDyadicRoot (operationDegree k + 1)
def operationSize (k : ℕ) : ℕ := 2 ^ operationHeight k
def operationPadding (k : ℕ) : FreeMonoid Bool :=
  FreeMonoid.ofList (List.replicate (operationSize k - 1 - operationDegree k) false)

theorem operationHeight_pos (k : ℕ) : 0 < operationHeight k :=
  strictDyadicRoot_pos _

theorem operationSize_bound (k : ℕ) : operationDegree k + 1 < operationSize k :=
  lt_strictDyadicRoot_pow _

theorem operationPadding_length (k : ℕ) :
    (operationPadding k).length = operationSize k - 1 - operationDegree k := by
  simp [operationPadding, FreeMonoid.length]

theorem operation_block_count (k : ℕ) :
    operationDegree k + (operationPadding k).length + 1 = operationSize k := by
  rw [operationPadding_length]
  have h := operationSize_bound k
  omega

theorem operation_reset_degree (h k : ℕ) :
    localResetDegree (2 ^ h - 1) k (operationPadding k) =
      2 ^ (h + operationHeight k) - 1 := by
  let n := 2 ^ h - 1
  have hn : n + 1 = 2 ^ h := by
    have hp : 0 < (2 : ℕ) ^ h := pow_pos (by norm_num) _
    dsimp [n]
    omega
  have hs : localResetDegree n k (operationPadding k) + 1 = operationSize k * (n + 1) := by
    unfold localResetDegree
    change (operationDegree k + (operationPadding k).length) * (n + 1) + n + 1 = _
    calc
      _ = (operationDegree k + (operationPadding k).length + 1) * (n + 1) := by ring
      _ = _ := by rw [operation_block_count]
  rw [hn] at hs
  have hp : operationSize k * 2 ^ h = 2 ^ (h + operationHeight k) := by
    rw [operationSize, pow_add]
    exact Nat.mul_comm _ _
  rw [hp] at hs
  dsimp [n] at hs
  omega

def resetPrefix (P : PrefixState F) (k : ℕ) : PrefixState F where
  height := P.height + operationHeight k
  polynomial := localResetStem F (2 ^ P.height - 1) (prefixCoefficients F P) k (operationPadding k)
  homogeneous := by
    have h := localResetStem_homogeneous F (2 ^ P.height - 1)
      (prefixCoefficients F P) k (operationPadding k)
    change WordHomogeneous (localResetDegree (2 ^ P.height - 1) k (operationPadding k)) _ at h
    rw [operation_reset_degree] at h
    exact h
  nonzero := localResetStem_ne_zero F _ _ (prefixCoefficients_nonzero F P) _ _

@[simp] theorem resetPrefix_height (P : PrefixState F) (k : ℕ) :
    (resetPrefix F P k).height = P.height + operationHeight k := rfl

theorem resetPrefix_space_containment (P : PrefixState F) (k : ℕ) :
    prefixSpace F (resetPrefix F P k).polynomial ≤
      blockPower F (prefixSpace F P.polynomial) (operationSize k) := by
  have h := resetSpace_le_blockPower F (2 ^ P.height - 1) (prefixCoefficients F P)
    k (operationPadding k)
  rw [stemSpace_eq_prefixSpace, stemPolynomial_localResetCoefficients] at h
  rw [stemSpace_eq_prefixSpace, prefixCoefficients_readback] at h
  change prefixSpace F (resetPrefix F P k).polynomial ≤ _ at h
  change prefixSpace F (resetPrefix F P k).polynomial ≤
    blockPower F (prefixSpace F P.polynomial)
      (operationDegree k + (operationPadding k).length + 1) at h
  simpa only [operation_block_count] using h

theorem resetPrefix_space_killed (C : Type*) [CommRing C] [Algebra F C]
    (P : PrefixState F) (k : ℕ)
    (f : WordAlgebra F →ₐ[F] Matrix (Fin k) (Fin k) C) :
    prefixSpace F (resetPrefix F P k).polynomial ≤ LinearMap.ker f.toLinearMap := by
  have h := resetSpace_le_matrix_kernel F C (2 ^ P.height - 1) (prefixCoefficients F P)
    k (operationPadding k) f
  rw [stemSpace_eq_prefixSpace, stemPolynomial_localResetCoefficients] at h
  exact h

end

end CriticalGK2.Actual
