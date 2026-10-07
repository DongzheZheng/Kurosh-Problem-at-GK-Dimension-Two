import CriticalGK2.LocalOperation

/-!
# Actual block-power containment of the local PI operation

The repeated block space is the linear span of genuine products of the two
physical stem blocks.  A homogeneous source polynomial expands into such
products.  The local PI operation consequently lives in the intended repeated
block space, including the padding blocks.
-/

namespace CriticalGK2

open scoped BigOperators

/-- A product of the two actual physical stem blocks, with its source word. -/
noncomputable def physicalBlockProduct (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (w : FreeMonoid Bool) : BinaryFreeAlgebra F :=
  (w.toList.map fun b => stemEmbedding F n t (binaryLetter F b)).prod

/-- The concrete repeated block space, formed by taking linear spans of products. -/
noncomputable def repeatedBlockSpace (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (m : ℕ) : Submodule F (BinaryFreeAlgebra F) :=
  Submodule.span F {z | ∃ w : FreeMonoid Bool,
    w.length = m ∧ z = physicalBlockProduct F n t w}

/-- Word evaluation under any free-algebra map is its actual ordered letter product. -/
theorem freeMonoidAlgebra_hom_word {F A : Type*} [Field F] [Ring A] [Algebra F A]
    (f : BinaryFreeAlgebra F →ₐ[F] A) (w : FreeMonoid Bool) :
    f (MonoidAlgebra.single w 1) =
      (w.toList.map fun b => f (binaryLetter F b)).prod := by
  have hf : f = binaryEvaluation F A (fun b => f (binaryLetter F b)) := by
    apply freeMonoidAlgebra_hom_ext_letters
    intro b
    simp [binaryEvaluation, binaryLetter]
  calc
    f (MonoidAlgebra.single w 1) =
        binaryEvaluation F A (fun b => f (binaryLetter F b))
          (MonoidAlgebra.single w 1) := DFunLike.congr_fun hf _
    _ = (w.toList.map fun b => f (binaryLetter F b)).prod := by
      simp [binaryEvaluation, FreeMonoid.lift_apply]

/-- Stem substitution sends a source word to an actual physical block product. -/
theorem stemEmbedding_word (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (w : FreeMonoid Bool) :
    stemEmbedding F n t (MonoidAlgebra.single w 1) = physicalBlockProduct F n t w :=
  freeMonoidAlgebra_hom_word (stemEmbedding F n t) w

/-- All coefficients of a homogeneous polynomial contribute products with the
same number of physical blocks.  This verifies containment by expansion. -/
theorem stemEmbedding_mem_repeatedBlockSpace (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (m : ℕ) (P : BinaryFreeAlgebra F)
    (hP : WordHomogeneous m P) :
    stemEmbedding F n t P ∈ repeatedBlockSpace F n t m := by
  classical
  rw [MonoidAlgebra.lift_unique (stemEmbedding F n t) P]
  change (∑ w ∈ P.support, P w • stemEmbedding F n t (MonoidAlgebra.single w 1)) ∈ _
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨w, hP w (Finsupp.mem_support_iff.mp hw), ?_⟩
  exact stemEmbedding_word F n t w

/-- The padded local PI is built entirely from the original two stem blocks. -/
theorem localPIBlock_mem_repeatedBlockSpace (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool) :
    localPIBlock F n t k u ∈
      repeatedBlockSpace F n t ((k * k + 1) * (k * k + 1) + u.length) := by
  apply stemEmbedding_mem_repeatedBlockSpace
  exact wordHomogeneous_mul (codedMatrixPI_homogeneous F (k * k + 1))
    (wordHomogeneous_single u (1 : F))

end CriticalGK2
