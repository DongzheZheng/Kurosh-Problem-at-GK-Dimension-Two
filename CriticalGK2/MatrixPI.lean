import Mathlib

/-!
# A universal matrix polynomial identity

The alternating product of more than `k * k` matrices vanishes over every
commutative coefficient ring. The proof uses the standard matrix basis
and a pigeonhole argument.
-/

namespace CriticalGK2

open scoped BigOperators

/-- The ordinary noncommutative alternating product, bundled as an alternating map. -/
noncomputable def alternatingProduct (R A : Type*) [CommRing R] [Ring A]
    [Algebra R A] (p : ℕ) : AlternatingMap R A A (Fin p) :=
  (MultilinearMap.mkPiAlgebraFin R p A).alternatization

/-- Unfolding the alternating product gives the usual signed permutation sum. -/
theorem alternatingProduct_apply (R A : Type*) [CommRing R] [Ring A]
    [Algebra R A] (p : ℕ) (v : Fin p → A) :
    alternatingProduct R A p v =
      ∑ σ : Equiv.Perm (Fin p), Equiv.Perm.sign σ • (List.ofFn fun i => v (σ i)).prod := by
  classical
  simp [alternatingProduct, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]

/-- Every alternating map on `p > k²` matrix arguments vanishes.

`Matrix.stdBasis` has the index type `Fin k × Fin k`.  An injective family of
`p` different basis elements would force `p ≤ k²`, contradicting the hypothesis.
-/
theorem alternating_matrix_map_eq_zero (R : Type*) [CommRing R]
    (k p : ℕ) (hp : k * k < p)
    (f : AlternatingMap R (Matrix (Fin k) (Fin k) R)
      (Matrix (Fin k) (Fin k) R) (Fin p)) : f = 0 := by
  classical
  apply (Matrix.stdBasis R (Fin k) (Fin k)).ext_alternating
  intro v hv
  have hcard := Fintype.card_le_of_injective v hv
  simp only [Fintype.card_fin, Fintype.card_prod] at hcard
  omega

/-- The signed product sum is zero over an arbitrary commutative ring.

The result includes characteristic two and rings with zero divisors.
-/
theorem matrix_alternating_product_eq_zero (R : Type*) [CommRing R]
    (k p : ℕ) (hp : k * k < p)
    (v : Fin p → Matrix (Fin k) (Fin k) R) :
    alternatingProduct R (Matrix (Fin k) (Fin k) R) p v = 0 := by
  have hf := alternating_matrix_map_eq_zero R k p hp
    (alternatingProduct R (Matrix (Fin k) (Fin k) R) p)
  exact congrArg (fun g => g v) hf

/-- Explicit permutation-sum form of the matrix polynomial identity. -/
theorem matrix_signed_product_sum_eq_zero (R : Type*) [CommRing R]
    (k p : ℕ) (hp : k * k < p)
    (v : Fin p → Matrix (Fin k) (Fin k) R) :
    (∑ σ : Equiv.Perm (Fin p),
      Equiv.Perm.sign σ • (List.ofFn fun i => v (σ i)).prod) = 0 := by
  rw [← alternatingProduct_apply R (Matrix (Fin k) (Fin k) R) p v]
  exact matrix_alternating_product_eq_zero R k p hp v


/-- A length-`p` binary codeword for `i`, with its unique `true` bit at `i`.

Each codeword has length `p`. The resulting polynomial degree depends
only on `p`, as required by sparse scheduling.
-/
def oneHotCode (p : ℕ) (i : Fin p) : List Bool :=
  List.ofFn fun j : Fin p => decide (j = i)

@[simp]
theorem oneHotCode_length (p : ℕ) (i : Fin p) : (oneHotCode p i).length = p := by
  simp [oneHotCode]

theorem oneHotCode_injective (p : ℕ) : Function.Injective (oneHotCode p) := by
  intro i j h
  change List.ofFn (fun a : Fin p => decide (a = i)) =
    List.ofFn (fun a : Fin p => decide (a = j)) at h
  have hi : decide (i = j) = true := by
    simpa using (congrFun (List.ofFn_injective h) i).symm
  exact of_decide_eq_true hi

/-- A positive fixed-length injective code induces an injective encoding of lists. -/
theorem fixedLength_flatMap_injective {ι α : Type*} (code : ι → List α)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (hlen : ∀ i, (code i).length = ℓ)
    (hinj : Function.Injective code) : Function.Injective (fun l : List ι => l.flatMap code) := by
  intro l
  induction l with
  | nil =>
      intro l' h
      cases l' with
      | nil => rfl
      | cons b bs =>
          have hl := congrArg List.length h
          simp only [List.flatMap_nil, List.length_nil, List.flatMap_cons,
            List.length_append, hlen] at hl
          omega
  | cons a as ih =>
      intro l' h
      cases l' with
      | nil =>
          have hl := congrArg List.length h
          simp only [List.flatMap_nil, List.length_nil, List.flatMap_cons,
            List.length_append, hlen] at hl
          omega
      | cons b bs =>
          have hhead : code a = code b := by
            have ht := congrArg (List.take ℓ) h
            simpa only [List.flatMap_cons, List.take_left' (hlen a),
              List.take_left' (hlen b)] using ht
          have hab := hinj hhead
          subst b
          have htail : as.flatMap code = bs.flatMap code := by
            apply List.append_cancel_left
            simpa only [List.flatMap_cons] using h
          exact congrArg (List.cons a) (ih htail)

/-- The binary word associated to a permutation of the coded variables. -/
def encodedPermutation (p : ℕ) (σ : Equiv.Perm (Fin p)) : FreeMonoid Bool :=
  FreeMonoid.ofList ((List.ofFn fun i => σ i).flatMap (oneHotCode p))

/-- Different permutations yield different binary words, by fixed-length decoding. -/
theorem encodedPermutation_injective (p : ℕ) (hp : 0 < p) :
    Function.Injective (encodedPermutation p) := by
  intro σ τ h
  have hlist : (List.ofFn fun i => σ i).flatMap (oneHotCode p) =
      (List.ofFn fun i => τ i).flatMap (oneHotCode p) :=
    congrArg FreeMonoid.toList h
  have hfn := List.ofFn_injective
    (fixedLength_flatMap_injective (oneHotCode p) p hp
      (oneHotCode_length p) (oneHotCode_injective p) hlist)
  exact Equiv.ext fun i => congrFun hfn i

/-- Encoding a list with length-`ℓ` blocks multiplies its length by `ℓ`. -/
theorem fixedLength_flatMap_length {ι α : Type*} (code : ι → List α)
    (ℓ : ℕ) (hlen : ∀ i, (code i).length = ℓ) (l : List ι) :
    (l.flatMap code).length = l.length * ℓ := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.flatMap_cons, List.length_append, hlen, ih, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega

@[simp]
theorem encodedPermutation_length (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    (encodedPermutation p σ).length = p * p := by
  change ((List.ofFn fun i => σ i).flatMap (oneHotCode p)).length = p * p
  rw [fixedLength_flatMap_length (oneHotCode p) p (oneHotCode_length p)]
  simp

/-- The free associative algebra on the two-element alphabet `Bool`. -/
abbrev BinaryFreeAlgebra (R : Type*) [CommRing R] := MonoidAlgebra R (FreeMonoid Bool)

/-- Taking one word coefficient is an additive homomorphism. -/
theorem binaryFinsetSum_apply {ι R : Type*} [CommRing R]
    (s : Finset ι) (f : ι → BinaryFreeAlgebra R) (w : FreeMonoid Bool) :
    (∑ i ∈ s, f i) w = ∑ i ∈ s, f i w := by
  let ev : BinaryFreeAlgebra R →+ R :=
    { toFun := fun P => P w
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum ev f s

/-- The coded alternating polynomial, over any commutative coefficient ring. -/
noncomputable def codedMatrixPI (R : Type*) [CommRing R] (p : ℕ) : BinaryFreeAlgebra R :=
  ∑ σ : Equiv.Perm (Fin p),
    Equiv.Perm.sign σ • MonoidAlgebra.single (encodedPermutation p σ) (1 : R)

/-- The coefficient of the identity-permutation word is exactly one. -/
theorem codedMatrixPI_identity_coefficient (R : Type*) [CommRing R]
    (p : ℕ) (hp : 0 < p) :
    codedMatrixPI R p (encodedPermutation p (1 : Equiv.Perm (Fin p))) = 1 := by
  classical
  change (∑ σ : Equiv.Perm (Fin p),
    Equiv.Perm.sign σ • MonoidAlgebra.single (encodedPermutation p σ) (1 : R))
      (encodedPermutation p 1) = 1
  rw [binaryFinsetSum_apply]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin p))]
  · simp
  · intro σ _ hσ
    have hword : encodedPermutation p σ ≠ encodedPermutation p 1 := by
      intro heq
      exact hσ (encodedPermutation_injective p hp heq)
    change Equiv.Perm.sign σ •
      (MonoidAlgebra.single (encodedPermutation p σ) (1 : R)
        (encodedPermutation p 1)) = 0
    rw [MonoidAlgebra.single_apply, if_neg hword, smul_zero]
  · simp

/-- Nonzero in every characteristic, since the distinguished word has coefficient one. -/
theorem codedMatrixPI_ne_zero (R : Type*) [CommRing R] [Nontrivial R]
    (p : ℕ) (hp : 0 < p) : codedMatrixPI R p ≠ 0 := by
  intro h
  have hc := codedMatrixPI_identity_coefficient R p hp
  rw [h] at hc
  exact zero_ne_one (by simpa using hc)

/-- All nonzero coefficients of the coded polynomial have the same word degree. -/
theorem codedMatrixPI_homogeneous (R : Type*) [CommRing R]
    (p : ℕ) (w : FreeMonoid Bool) (hw : codedMatrixPI R p w ≠ 0) :
    w.length = p * p := by
  classical
  by_contra hlen
  apply hw
  change (∑ σ : Equiv.Perm (Fin p),
    Equiv.Perm.sign σ • MonoidAlgebra.single (encodedPermutation p σ) (1 : R)) w = 0
  rw [binaryFinsetSum_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hword : encodedPermutation p σ ≠ w := by
    intro heq
    apply hlen
    rw [← heq, encodedPermutation_length]
  change Equiv.Perm.sign σ •
    (MonoidAlgebra.single (encodedPermutation p σ) (1 : R) w) = 0
  rw [MonoidAlgebra.single_apply, if_neg hword, smul_zero]

/-- Evaluation of the free binary algebra at two algebra elements. -/
noncomputable def binaryEvaluation (R A : Type*) [CommRing R] [Ring A]
    [Algebra R A] (v : Bool → A) : BinaryFreeAlgebra R →ₐ[R] A :=
  MonoidAlgebra.lift R A (FreeMonoid Bool) (FreeMonoid.lift v)

/-- Word evaluation respects a concatenation of code blocks. -/
theorem wordEvaluation_flatMap {ι A : Type*} [Monoid A]
    (v : Bool → A) (code : ι → List Bool) (l : List ι) :
    FreeMonoid.lift v (FreeMonoid.ofList (l.flatMap code)) =
      (l.map fun i => FreeMonoid.lift v (FreeMonoid.ofList (code i))).prod := by
  induction l with
  | nil => simp [FreeMonoid.lift_ofList]
  | cons a as ih =>
      simp only [List.flatMap_cons, List.map_cons, List.prod_cons]
      change FreeMonoid.lift v (FreeMonoid.ofList (code a) *
        FreeMonoid.ofList (as.flatMap code)) = _
      rw [map_mul, ih]

/-- Evaluating the coded polynomial recovers an actual alternating matrix product. -/
theorem binaryEvaluation_codedMatrixPI (R A : Type*) [CommRing R] [Ring A]
    [Algebra R A] (p : ℕ) (v : Bool → A) :
    binaryEvaluation R A v (codedMatrixPI R p) =
      alternatingProduct R A p
        (fun i => FreeMonoid.lift v (FreeMonoid.ofList (oneHotCode p i))) := by
  classical
  rw [alternatingProduct_apply]
  simp only [binaryEvaluation, codedMatrixPI, map_sum, Units.smul_def, map_zsmul,
    MonoidAlgebra.lift_single, one_smul]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact (wordEvaluation_flatMap v (oneHotCode p) (List.ofFn fun i => σ i)).trans
    (by simp only [List.map_ofFn]; rfl)

/-- The binary polynomial vanishes under every evaluation in `k × k` matrices. -/
theorem binaryEvaluation_codedMatrixPI_eq_zero (R : Type*) [CommRing R]
    (k p : ℕ) (hp : k * k < p)
    (v : Bool → Matrix (Fin k) (Fin k) R) :
    binaryEvaluation R (Matrix (Fin k) (Fin k) R) v (codedMatrixPI R p) = 0 := by
  rw [binaryEvaluation_codedMatrixPI]
  exact matrix_alternating_product_eq_zero R k p hp _

/-- The polynomial over the base ring also annihilates matrices over every
commutative coefficient algebra.  In particular this applies to polynomial
coefficient rings and to arbitrary field extensions. -/
theorem binaryEvaluation_codedMatrixPI_matrix_over_algebra
    (R C : Type*) [CommRing R] [CommRing C] [Algebra R C]
    (k p : ℕ) (hp : k * k < p)
    (v : Bool → Matrix (Fin k) (Fin k) C) :
    binaryEvaluation R (Matrix (Fin k) (Fin k) C) v (codedMatrixPI R p) = 0 := by
  rw [binaryEvaluation_codedMatrixPI, alternatingProduct_apply]
  exact matrix_signed_product_sum_eq_zero C k p hp
    (fun i : Fin p => FreeMonoid.lift v (FreeMonoid.ofList (oneHotCode p i)))

/-- Right multiplication by a word preserves its corresponding coefficient. -/
theorem binaryMonomial_right_coefficient (R : Type*) [CommRing R]
    (P : BinaryFreeAlgebra R) (w u : FreeMonoid Bool) :
    (P * MonoidAlgebra.single u (1 : R)) (w * u) = P w := by
  have heq := MonoidAlgebra.mul_single_apply_aux
    (x := P) (m := u) (m₁ := w * u) (m₂ := w) (r := (1 : R))
    (fun w' _ => mul_right_cancel_iff)
  simpa using heq

/-- The PI can be padded on the right without losing nonzeroness. -/
theorem codedMatrixPI_right_padding_ne_zero (R : Type*) [CommRing R] [Nontrivial R]
    (p : ℕ) (hp : 0 < p) (u : FreeMonoid Bool) :
    codedMatrixPI R p * MonoidAlgebra.single u (1 : R) ≠ 0 := by
  intro h
  have hc := binaryMonomial_right_coefficient R (codedMatrixPI R p)
    (encodedPermutation p (1 : Equiv.Perm (Fin p))) u
  rw [codedMatrixPI_identity_coefficient R p hp, h] at hc
  exact zero_ne_one (by simpa using hc)

/-- Padding preserves the universal matrix evaluation relation. -/
theorem codedMatrixPI_right_padding_evaluation_eq_zero
    (R C : Type*) [CommRing R] [CommRing C] [Algebra R C]
    (k p : ℕ) (hp : k * k < p)
    (v : Bool → Matrix (Fin k) (Fin k) C) (u : FreeMonoid Bool) :
    binaryEvaluation R (Matrix (Fin k) (Fin k) C) v
      (codedMatrixPI R p * MonoidAlgebra.single u (1 : R)) = 0 := by
  rw [map_mul, binaryEvaluation_codedMatrixPI_matrix_over_algebra R C k p hp v]
  exact zero_mul _

/-- Uniformly, a nonzero polynomial in two letters annihilates all `k × k` matrices. -/
theorem exists_nonzero_binary_matrixPI (R : Type*) [CommRing R] [Nontrivial R] (k : ℕ) :
    ∃ P : BinaryFreeAlgebra R, P ≠ 0 ∧
      ∀ v : Bool → Matrix (Fin k) (Fin k) R,
        binaryEvaluation R (Matrix (Fin k) (Fin k) R) v P = 0 := by
  refine ⟨codedMatrixPI R (k * k + 1), codedMatrixPI_ne_zero R _ (by omega), ?_⟩
  intro v
  exact binaryEvaluation_codedMatrixPI_eq_zero R k _ (by omega) v

end CriticalGK2
