import CriticalGK2.WordProducts
import CriticalGK2.LocalContainment
import CriticalGK2.StemPolynomial

/-!
# Actual multiplication powers of local block spaces

The spaces are actual submodules of the actual free word algebra. Their
concatenation, degrees and nonzero vectors are established from word
multiplication.
-/

namespace CriticalGK2.Actual

noncomputable section

open CriticalGK2

variable (F : Type*) [Field F]

def blockPower (S : Submodule F (WordAlgebra F)) : ℕ → Submodule F (WordAlgebra F)
  | 0 => homogeneous F 0
  | m + 1 => productSpan F (blockPower S m) S

@[simp] theorem blockPower_zero (S : Submodule F (WordAlgebra F)) :
    blockPower F S 0 = homogeneous F 0 := rfl

@[simp] theorem blockPower_succ (S : Submodule F (WordAlgebra F)) (m : ℕ) :
    blockPower F S (m + 1) = productSpan F (blockPower F S m) S := rfl

@[simp] theorem blockPower_one (S : Submodule F (WordAlgebra F)) :
    blockPower F S 1 = S := by
  rw [blockPower_succ, blockPower_zero, productSpan_homogeneous_zero_left]

theorem productSpan_blockPower (S : Submodule F (WordAlgebra F)) (m n : ℕ) :
    productSpan F (blockPower F S m) (blockPower F S n) = blockPower F S (m + n) := by
  induction n with
  | zero => simp [productSpan_homogeneous_zero_right]
  | succ n ih =>
      rw [blockPower_succ, ← productSpan_assoc, ih]
      rfl

theorem blockPower_le_homogeneous (S : Submodule F (WordAlgebra F))
    (q : ℕ) (hS : S ≤ homogeneous F q) (m : ℕ) :
    blockPower F S m ≤ homogeneous F (m * q) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h := productSpan_mono F ih hS
      simpa only [blockPower_succ, homogeneous_productSpan, Nat.succ_mul] using h

theorem pow_mem_blockPower (S : Submodule F (WordAlgebra F))
    (x : WordAlgebra F) (hx : x ∈ S) (m : ℕ) : x ^ m ∈ blockPower F S m := by
  induction m with
  | zero =>
      rw [pow_zero, blockPower_zero, homogeneous_zero_eq_span_one]
      exact Submodule.subset_span (by simp)
  | succ m ih =>
      rw [pow_succ, blockPower_succ]
      exact mul_mem_productSpan F ih hx

theorem blockPower_ne_bot (S : Submodule F (WordAlgebra F))
    (x : WordAlgebra F) (hx : x ∈ S) (hne : x ≠ 0) (m : ℕ) :
    blockPower F S m ≠ ⊥ := by
  intro h
  have hm := pow_mem_blockPower F S x hx m
  rw [h] at hm
  exact (pow_ne_zero m hne) ((Submodule.mem_bot F).mp hm)

def stemSpace (n : ℕ) (t : StemWord n → F) : Submodule F (WordAlgebra F) :=
  Submodule.span F (Set.range fun b : Bool =>
    stemEmbedding F n t (binaryLetter F b))

theorem physicalBlock_mem_stemSpace (n : ℕ) (t : StemWord n → F) (b : Bool) :
    stemEmbedding F n t (binaryLetter F b) ∈ stemSpace F n t :=
  Submodule.subset_span ⟨b, rfl⟩

theorem wordHomogeneous_mem_homogeneous (n : ℕ) (x : WordAlgebra F)
    (hx : WordHomogeneous n x) : x ∈ homogeneous F n := by
  rw [mem_homogeneous_iff]
  intro w hw
  by_contra h
  exact hw (hx w h)

theorem stemSpace_le_homogeneous (n : ℕ) (t : StemWord n → F) :
    stemSpace F n t ≤ homogeneous F (n + 1) := by
  apply Submodule.span_le.mpr
  rintro x ⟨b, rfl⟩
  exact wordHomogeneous_mem_homogeneous F _ _
    (stemEmbedding_binaryLetter_homogeneous F n t b)

theorem stemSpace_ne_bot (n : ℕ) (t : StemWord n → F) (ht : t ≠ 0) :
    stemSpace F n t ≠ ⊥ := by
  intro h
  have hx := physicalBlock_mem_stemSpace F n t false
  rw [h] at hx
  have hzero := (Submodule.mem_bot F).mp hx
  have hinj := stemEmbedding_injective F n t ht
  have hletter : binaryLetter F false = 0 := hinj (by simpa using hzero)
  exact (MonoidAlgebra.single_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)) hletter

theorem physicalBlockProduct_mem_blockPower (n : ℕ) (t : StemWord n → F)
    (w : FreeMonoid Bool) :
    physicalBlockProduct F n t w ∈ blockPower F (stemSpace F n t) w.length := by
  refine FreeMonoid.recOn w ?_ ?_
  · change (1 : WordAlgebra F) ∈ blockPower F (stemSpace F n t) 0
    simpa using pow_mem_blockPower F (stemSpace F n t)
      (stemEmbedding F n t (binaryLetter F false))
      (physicalBlock_mem_stemSpace F n t false) 0
  · intro b w ih
    have hprod := mul_mem_productSpan F (physicalBlock_mem_stemSpace F n t b) ih
    have hprod' :
        stemEmbedding F n t (binaryLetter F b) * physicalBlockProduct F n t w ∈
          productSpan F (blockPower F (stemSpace F n t) 1)
            (blockPower F (stemSpace F n t) w.length) := by
      simpa only [blockPower_one] using hprod
    rw [productSpan_blockPower] at hprod'
    simpa [physicalBlockProduct, FreeMonoid.toList_mul, FreeMonoid.length_mul,
      FreeMonoid.length_of, Nat.add_comm] using hprod'

theorem repeatedBlockSpace_le_blockPower (n : ℕ) (t : StemWord n → F) (m : ℕ) :
    repeatedBlockSpace F n t m ≤ blockPower F (stemSpace F n t) m := by
  apply Submodule.span_le.mpr
  rintro x ⟨w, hw, rfl⟩
  simpa only [hw] using physicalBlockProduct_mem_blockPower F n t w

theorem localPIBlock_mem_blockPower (n : ℕ) (t : StemWord n → F)
    (k : ℕ) (u : FreeMonoid Bool) :
    localPIBlock F n t k u ∈
      blockPower F (stemSpace F n t) ((k * k + 1) * (k * k + 1) + u.length) :=
  repeatedBlockSpace_le_blockPower F n t _
    (localPIBlock_mem_repeatedBlockSpace F n t k u)

end

end CriticalGK2.Actual
