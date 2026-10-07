import CriticalGK2.MatrixPI

/-!
# A local PI operation with an arbitrary linear-combination stem

The stem is an arbitrary coefficient vector on binary words of a fixed length.
Its nonzero coefficient yields a retraction of the free block substitution.
The block alphabet is then injected into the actual two-letter free algebra by
fixed-length decoding.
-/

namespace CriticalGK2

open scoped BigOperators

/-- Words of a fixed length, represented without quotienting or variable lengths. -/
abbrev StemWord (n : ℕ) := Fin n → Bool

/-- A physical block consists of a length-`n` stem word followed by one letter. -/
abbrev BlockAlphabet (n : ℕ) := StemWord n × Bool

abbrev BlockFreeAlgebra (F : Type*) [Field F] (n : ℕ) :=
  MonoidAlgebra F (FreeMonoid (BlockAlphabet n))

/-- The actual free letter in the binary monoid algebra. -/
noncomputable def binaryLetter (F : Type*) [CommRing F] (b : Bool) : BinaryFreeAlgebra F :=
  MonoidAlgebra.single (FreeMonoid.of b) 1

/-- Algebra maps out of a free monoid algebra are determined by their letters. -/
theorem freeMonoidAlgebra_hom_ext_letters
    {R α A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {f g : MonoidAlgebra R (FreeMonoid α) →ₐ[R] A}
    (h : ∀ a, f (MonoidAlgebra.single (FreeMonoid.of a) 1) =
      g (MonoidAlgebra.single (FreeMonoid.of a) 1)) : f = g := by
  apply MonoidAlgebra.algHom_ext'
  apply FreeMonoid.hom_eq
  intro a
  exact h a

/-- The block generator `t ⊗ b`, expanded in the genuine block-word basis. -/
noncomputable def stemBlock (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (b : Bool) : BlockFreeAlgebra F n :=
  ∑ a : StemWord n, t a • MonoidAlgebra.single (FreeMonoid.of (a, b)) 1

/-- Substitution of the two free letters by the two stem blocks. -/
noncomputable def stemSubstitution (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) : BinaryFreeAlgebra F →ₐ[F] BlockFreeAlgebra F n :=
  MonoidAlgebra.lift F (BlockFreeAlgebra F n) (FreeMonoid Bool)
    (FreeMonoid.lift (stemBlock F n t))

/-- A chosen nonzero stem coefficient gives an explicit decoding algebra map. -/
noncomputable def stemRetraction (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (a₀ : StemWord n) : BlockFreeAlgebra F n →ₐ[F] BinaryFreeAlgebra F :=
  MonoidAlgebra.lift F (BinaryFreeAlgebra F) (FreeMonoid (BlockAlphabet n))
    (FreeMonoid.lift fun g =>
      if g.1 = a₀ then (t a₀)⁻¹ • binaryLetter F g.2 else 0)

/-- Retraction reads the stem block as the original binary letter. -/
theorem stemRetraction_stemBlock (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (a₀ : StemWord n) (ha₀ : t a₀ ≠ 0) (b : Bool) :
    stemRetraction F n t a₀ (stemBlock F n t b) = binaryLetter F b := by
  classical
  simp only [stemBlock, stemRetraction, map_sum, map_smul,
    MonoidAlgebra.lift_single, FreeMonoid.lift_eval_of, one_smul]
  rw [Finset.sum_eq_single a₀]
  · simp [ha₀, smul_smul]
  · intro a _ ha
    simp [ha]
  · simp

/-- The decoding and substitution maps compose to the identity on all words. -/
theorem stemRetraction_comp_stemSubstitution (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (a₀ : StemWord n) (ha₀ : t a₀ ≠ 0) :
    (stemRetraction F n t a₀).comp (stemSubstitution F n t) =
      AlgHom.id F (BinaryFreeAlgebra F) := by
  apply freeMonoidAlgebra_hom_ext_letters
  intro b
  simp only [AlgHom.comp_apply, AlgHom.id_apply, stemSubstitution,
    MonoidAlgebra.lift_single, FreeMonoid.lift_eval_of, one_smul]
  exact stemRetraction_stemBlock F n t a₀ ha₀ b

/-- For every nonzero stem, substitution is injective on the entire free algebra. -/
theorem stemSubstitution_injective (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (ht : t ≠ 0) : Function.Injective (stemSubstitution F n t) := by
  classical
  have hex : ∃ a₀, t a₀ ≠ 0 := by
    by_contra! h
    exact ht (funext h)
  obtain ⟨a₀, ha₀⟩ := hex
  have hleft : Function.LeftInverse (stemRetraction F n t a₀) (stemSubstitution F n t) := by
    intro P
    exact DFunLike.congr_fun (stemRetraction_comp_stemSubstitution F n t a₀ ha₀) P
  exact hleft.injective

/-- The binary word corresponding to one physical block. -/
def blockWordCode (n : ℕ) (g : BlockAlphabet n) : List Bool :=
  List.ofFn g.1 ++ [g.2]

@[simp]
theorem blockWordCode_length (n : ℕ) (g : BlockAlphabet n) :
    (blockWordCode n g).length = n + 1 := by
  simp [blockWordCode]

/-- A physical block can be decoded uniquely into its stem and last letter. -/
theorem blockWordCode_injective (n : ℕ) : Function.Injective (blockWordCode n) := by
  intro g g' h
  rcases g with ⟨a, b⟩
  rcases g' with ⟨a', b'⟩
  change List.ofFn a ++ [b] = List.ofFn a' ++ [b'] at h
  have hhead : List.ofFn a = List.ofFn a' := by
    have ht := congrArg (List.take n) h
    have hl : (List.ofFn a ++ [b]).take n = List.ofFn a :=
      List.take_left' (by simp)
    have hr : (List.ofFn a' ++ [b']).take n = List.ofFn a' :=
      List.take_left' (by simp)
    exact hl.symm.trans (ht.trans hr)
  have ha := List.ofFn_injective hhead
  subst a'
  have hb : b = b' := List.singleton_injective (List.append_cancel_left h)
  subst b'
  rfl

/-- Flattening genuine fixed-length block words into binary words. -/
def flattenBlocks (n : ℕ) : FreeMonoid (BlockAlphabet n) →* FreeMonoid Bool where
  toFun w := FreeMonoid.ofList (w.toList.flatMap (blockWordCode n))
  map_one' := rfl
  map_mul' a b := by
    change (a.toList ++ b.toList).flatMap (blockWordCode n) =
      a.toList.flatMap (blockWordCode n) ++ b.toList.flatMap (blockWordCode n)
    simp only [List.flatMap_append]

/-- Equal-length parsing proves that flattening loses no block-word information. -/
theorem flattenBlocks_injective (n : ℕ) : Function.Injective (flattenBlocks n) := by
  intro u v h
  apply FreeMonoid.toList.injective
  apply fixedLength_flatMap_injective (blockWordCode n) (n + 1) (by omega)
    (blockWordCode_length n) (blockWordCode_injective n)
  exact congrArg FreeMonoid.toList h

/-- The linear and multiplicative block embedding into the actual binary free algebra. -/
noncomputable def flattenBlockAlgebra (F : Type*) [Field F] (n : ℕ) :
    BlockFreeAlgebra F n →ₐ[F] BinaryFreeAlgebra F :=
  MonoidAlgebra.mapDomainAlgHom F F (flattenBlocks n)

/-- Flattening is injective on all linear combinations, over the original field. -/
theorem flattenBlockAlgebra_injective (F : Type*) [Field F] (n : ℕ) :
    Function.Injective (flattenBlockAlgebra F n) := by
  exact MonoidAlgebra.mapDomain_injective (flattenBlocks_injective n)

/-- The actual arbitrary-stem substitution into the two-letter ambient free algebra. -/
noncomputable def stemEmbedding (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) : BinaryFreeAlgebra F →ₐ[F] BinaryFreeAlgebra F :=
  (flattenBlockAlgebra F n).comp (stemSubstitution F n t)

/-- Uniform freeness of the two stem blocks, proved through two explicit injections. -/
theorem stemEmbedding_injective (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (ht : t ≠ 0) : Function.Injective (stemEmbedding F n t) :=
  (flattenBlockAlgebra_injective F n).comp (stemSubstitution_injective F n t ht)

/-- Every algebra homomorphism to the relevant matrix algebra kills the coded PI. -/
theorem algHom_codedMatrixPI_eq_zero (F C : Type*) [Field F] [CommRing C] [Algebra F C]
    (k p : ℕ) (hp : k * k < p)
    (f : BinaryFreeAlgebra F →ₐ[F] Matrix (Fin k) (Fin k) C) :
    f (codedMatrixPI F p) = 0 := by
  have hf : f = binaryEvaluation F (Matrix (Fin k) (Fin k) C)
      (fun b => f (binaryLetter F b)) := by
    apply freeMonoidAlgebra_hom_ext_letters
    intro b
    simp [binaryEvaluation, binaryLetter]
  rw [hf]
  exact binaryEvaluation_codedMatrixPI_matrix_over_algebra F C k p hp _

/-- Injectivity preserves the nonzero PI under an arbitrary nonzero stem. -/
theorem stemEmbedding_codedMatrixPI_ne_zero (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (ht : t ≠ 0) (p : ℕ) (hp : 0 < p) :
    stemEmbedding F n t (codedMatrixPI F p) ≠ 0 := by
  intro h
  apply codedMatrixPI_ne_zero F p hp
  apply stemEmbedding_injective F n t ht
  simpa using h

/-- Actual ambient matrix evaluation of the stem-substituted PI vanishes. -/
theorem stemEmbedding_codedMatrixPI_evaluation_eq_zero
    (F C : Type*) [Field F] [CommRing C] [Algebra F C]
    (n : ℕ) (t : StemWord n → F) (k p : ℕ) (hp : k * k < p)
    (v : Bool → Matrix (Fin k) (Fin k) C) :
    binaryEvaluation F (Matrix (Fin k) (Fin k) C) v
      (stemEmbedding F n t (codedMatrixPI F p)) = 0 := by
  exact algHom_codedMatrixPI_eq_zero F C k p hp
    ((binaryEvaluation F (Matrix (Fin k) (Fin k) C) v).comp (stemEmbedding F n t))

/-- Appending a monomial preserves nonzeroness for every nonzero binary polynomial. -/
theorem binaryRightPadding_ne_zero (F : Type*) [Field F]
    (P : BinaryFreeAlgebra F) (hP : P ≠ 0) (u : FreeMonoid Bool) :
    P * MonoidAlgebra.single u 1 ≠ 0 := by
  intro h
  apply hP
  ext w
  have hc := binaryMonomial_right_coefficient F P w u
  rw [h] at hc
  simpa using hc.symm

/-- A word-degree condition on a polynomial, stated on actual coefficients. -/
def WordHomogeneous {F α : Type*} [Field F] (d : ℕ)
    (P : MonoidAlgebra F (FreeMonoid α)) : Prop :=
  ∀ w, P w ≠ 0 → w.length = d

theorem wordHomogeneous_zero {F α : Type*} [Field F] (d : ℕ) :
    WordHomogeneous d (0 : MonoidAlgebra F (FreeMonoid α)) := by
  intro w hw
  exact (hw rfl).elim

theorem wordHomogeneous_single {F α : Type*} [Field F]
    (w : FreeMonoid α) (c : F) :
    WordHomogeneous w.length (MonoidAlgebra.single w c) := by
  classical
  intro v hv
  by_cases h : w = v
  · simpa only [← h]
  · rw [MonoidAlgebra.single_apply, if_neg h] at hv
    exact (hv rfl).elim

theorem wordHomogeneous_smul {F α : Type*} [Field F] {d : ℕ}
    {P : MonoidAlgebra F (FreeMonoid α)} (hP : WordHomogeneous d P) (c : F) :
    WordHomogeneous d (c • P) := by
  intro w hw
  change c * P w ≠ 0 at hw
  exact hP w (mul_ne_zero_iff.mp hw).2

theorem wordHomogeneous_add {F α : Type*} [Field F] {d : ℕ}
    {P Q : MonoidAlgebra F (FreeMonoid α)}
    (hP : WordHomogeneous d P) (hQ : WordHomogeneous d Q) :
    WordHomogeneous d (P + Q) := by
  intro w hw
  by_cases hp : P w = 0
  · apply hQ w
    intro hq
    apply hw
    change P w + Q w = 0
    rw [hp, hq, add_zero]
  · exact hP w hp

theorem wordHomogeneous_sum {F α ι : Type*} [Field F]
    (d : ℕ) (s : Finset ι) (f : ι → MonoidAlgebra F (FreeMonoid α))
    (h : ∀ i ∈ s, WordHomogeneous d (f i)) :
    WordHomogeneous d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact wordHomogeneous_zero d
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact wordHomogeneous_add (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem wordHomogeneous_mul {F α : Type*} [Field F] {d e : ℕ}
    {P Q : MonoidAlgebra F (FreeMonoid α)}
    (hP : WordHomogeneous d P) (hQ : WordHomogeneous e Q) :
    WordHomogeneous (d + e) (P * Q) := by
  classical
  intro w hw
  have hwm : w ∈ (P * Q).support := Finsupp.mem_support_iff.mpr hw
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp (MonoidAlgebra.support_mul P Q hwm)
  rw [FreeMonoid.length_mul, hP u (Finsupp.mem_support_iff.mp hu),
    hQ v (Finsupp.mem_support_iff.mp hv)]

/-- If all letters are sent to degree `q`, a source word of degree `m` is sent to
an actual homogeneous polynomial of degree `m*q`. -/
theorem wordHomogeneous_algHom_word {F α : Type*} [Field F]
    (f : BinaryFreeAlgebra F →ₐ[F] MonoidAlgebra F (FreeMonoid α))
    (q : ℕ) (hf : ∀ b, WordHomogeneous q (f (binaryLetter F b)))
    (w : FreeMonoid Bool) :
    WordHomogeneous (w.length * q) (f (MonoidAlgebra.single w 1)) := by
  have hlist : ∀ l : List Bool,
      WordHomogeneous (l.length * q) (f (MonoidAlgebra.single (FreeMonoid.ofList l) 1)) := by
    intro l
    induction l with
    | nil =>
        have hs : MonoidAlgebra.single (FreeMonoid.ofList ([] : List Bool)) (1 : F) =
            (1 : BinaryFreeAlgebra F) := by
          simp [MonoidAlgebra.one_def]
        rw [hs, map_one]
        simpa only [List.length_nil, Nat.zero_mul, FreeMonoid.length_one,
          MonoidAlgebra.one_def] using
          (wordHomogeneous_single (1 : FreeMonoid α) (1 : F))
    | cons b bs ih =>
        have hmul : MonoidAlgebra.single (FreeMonoid.ofList (b :: bs)) (1 : F) =
            binaryLetter F b * MonoidAlgebra.single (FreeMonoid.ofList bs) 1 := by
          simp [binaryLetter, FreeMonoid.ofList_cons]
        rw [hmul, map_mul]
        have hh := wordHomogeneous_mul (hf b) ih
        convert hh using 1
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
  exact hlist w.toList

/-- General homogeneous polynomials are sent to the corresponding scaled degree;
the proof expands every actual coefficient of the source polynomial. -/
theorem wordHomogeneous_algHom {F α : Type*} [Field F]
    (f : BinaryFreeAlgebra F →ₐ[F] MonoidAlgebra F (FreeMonoid α))
    (q m : ℕ) (hf : ∀ b, WordHomogeneous q (f (binaryLetter F b)))
    (P : BinaryFreeAlgebra F) (hP : WordHomogeneous m P) :
    WordHomogeneous (m * q) (f P) := by
  rw [MonoidAlgebra.lift_unique f P]
  change WordHomogeneous (m * q)
    (∑ w ∈ P.support, P w • f (MonoidAlgebra.single w 1))
  apply wordHomogeneous_sum
  intro w hw
  have hd := hP w (Finsupp.mem_support_iff.mp hw)
  have hh := wordHomogeneous_algHom_word f q hf w
  rw [hd] at hh
  exact wordHomogeneous_smul hh (P w)

/-- The physical stem block is exactly its length-`n+1` word expansion. -/
theorem stemEmbedding_binaryLetter (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (b : Bool) :
    stemEmbedding F n t (binaryLetter F b) =
      ∑ a : StemWord n, t a •
        MonoidAlgebra.single (FreeMonoid.ofList (blockWordCode n (a, b))) 1 := by
  classical
  simp only [stemEmbedding, AlgHom.comp_apply, stemSubstitution, binaryLetter,
    MonoidAlgebra.lift_single, FreeMonoid.lift_eval_of, one_smul, stemBlock, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul]
  congr 1
  change MonoidAlgebra.mapDomain (flattenBlocks n)
    (MonoidAlgebra.single (FreeMonoid.of (a, b)) (1 : F)) = _
  rw [MonoidAlgebra.mapDomain_single]
  congr 1
  simp [flattenBlocks]

theorem stemEmbedding_binaryLetter_homogeneous (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (b : Bool) :
    WordHomogeneous (n + 1) (stemEmbedding F n t (binaryLetter F b)) := by
  rw [stemEmbedding_binaryLetter]
  apply wordHomogeneous_sum
  intro a _
  apply wordHomogeneous_smul
  simpa only [FreeMonoid.length, FreeMonoid.toList_ofList, blockWordCode_length] using
    (wordHomogeneous_single (FreeMonoid.ofList (blockWordCode n (a, b))) (1 : F))

/-- The genuine local zero-evaluation block in the ambient two-letter algebra. -/
noncomputable def localPIBlock (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool) : BinaryFreeAlgebra F :=
  stemEmbedding F n t (codedMatrixPI F (k * k + 1) * MonoidAlgebra.single u 1)

/-- Local block nonzeroness needs only the nonzero arbitrary stem. -/
theorem localPIBlock_ne_zero (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (ht : t ≠ 0) (k : ℕ) (u : FreeMonoid Bool) :
    localPIBlock F n t k u ≠ 0 := by
  intro h
  apply codedMatrixPI_right_padding_ne_zero F (k * k + 1) (by omega) u
  apply stemEmbedding_injective F n t ht
  simpa only [localPIBlock, map_zero] using h

/-- The local block vanishes under every matrix evaluation over every coefficient algebra. -/
theorem localPIBlock_evaluation_eq_zero
    (F C : Type*) [Field F] [CommRing C] [Algebra F C]
    (n : ℕ) (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool)
    (v : Bool → Matrix (Fin k) (Fin k) C) :
    binaryEvaluation F (Matrix (Fin k) (Fin k) C) v (localPIBlock F n t k u) = 0 := by
  simp only [localPIBlock, map_mul]
  rw [stemEmbedding_codedMatrixPI_evaluation_eq_zero F C n t k _ (by omega) v]
  exact zero_mul _

/-- The local operation stays in one precise physical word degree. -/
theorem localPIBlock_homogeneous (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool) :
    WordHomogeneous (((k * k + 1) * (k * k + 1) + u.length) * (n + 1))
      (localPIBlock F n t k u) := by
  apply wordHomogeneous_algHom (stemEmbedding F n t) (n + 1)
    ((k * k + 1) * (k * k + 1) + u.length)
    (stemEmbedding_binaryLetter_homogeneous F n t)
  exact wordHomogeneous_mul (codedMatrixPI_homogeneous F (k * k + 1))
    (wordHomogeneous_single u (1 : F))

end CriticalGK2
