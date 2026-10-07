import Mathlib.Algebra.Algebra.Unitization
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Matrix nilpotence implies algebraicity of the unitization

Let `A` be an associative non-unital algebra over a field `K`. If every matrix
over `A` is nilpotent, every matrix over `Unitization K A` is algebraic over `K`.

The proof applies the characteristic polynomial to the scalar projection.
Cayley--Hamilton places its value in the nil kernel, and a power of that
polynomial annihilates the original matrix.
-/

namespace CriticalGK2

open Polynomial

/-- Powers with strictly positive exponent, defined without adjoining an identity.
`positivePower x e` is the ordinary power `x ^ (e + 1)` when an identity exists. -/
def positivePower {R : Type*} [Mul R] (x : R) : ℕ → R
  | 0 => x
  | e + 1 => x * positivePower x e

theorem positivePower_eq_pow {R : Type*} [Monoid R] (x : R) (e : ℕ) :
    positivePower x e = x ^ (e + 1) := by
  induction e with
  | zero => simp [positivePower]
  | succ e ih =>
      change x * positivePower x e = x ^ (e + 1 + 1)
      rw [ih]
      exact (pow_succ' x (e + 1)).symm

/-- An algebra mapping to a matrix algebra over a field, with nil kernel,
is algebraic over that field. -/
theorem isAlgebraic_of_matrix_quotient_nil_kernel
    {K C n : Type*} [Field K] [Ring C] [Algebra K C]
    [Fintype n] [DecidableEq n]
    (π : C →ₐ[K] Matrix n n K)
    (kernelNil : ∀ z : C, π z = 0 → IsNilpotent z)
    (z : C) : IsAlgebraic K z := by
  let p : K[X] := (π z).charpoly
  have hp : p ≠ 0 := (Matrix.charpoly_monic (π z)).ne_zero
  have hkernel : π (aeval z p) = 0 := by
    rw [← Polynomial.aeval_algHom_apply]
    exact Matrix.aeval_self_charpoly (π z)
  obtain ⟨e, he⟩ := kernelNil (aeval z p) hkernel
  refine ⟨p ^ e, pow_ne_zero e hp, ?_⟩
  simpa only [map_pow] using he

section Unitization

variable {K A n : Type*} [Field K] [NonUnitalRing A] [Module K A]
  [IsScalarTower K A A] [SMulCommClass K A A]
  [Fintype n] [DecidableEq n]

/-- Coercing matrices into their actual unitization preserves all positive powers. -/
theorem unitization_map_positivePower (M : Matrix n n A) (e : ℕ) :
    (positivePower M e).map (Unitization.inrNonUnitalAlgHom K A) =
      positivePower (M.map (Unitization.inrNonUnitalAlgHom K A)) e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [positivePower, Matrix.map_mul, ih]
      rfl

/-- Actual scalar-kernel matrices in the unitization are nilpotent, assuming
that every matrix over the underlying non-unital algebra is nilpotent. -/
theorem unitization_matrix_kernel_nil
    (matrixNil : ∀ M : Matrix n n A, ∃ e : ℕ, positivePower M e = 0)
    (T : Matrix n n (Unitization K A))
    (hT : (Unitization.fstHom K A).mapMatrix T = 0) : IsNilpotent T := by
  let M : Matrix n n A := T.map (fun x => x.snd)
  have hM : M.map (Unitization.inrNonUnitalAlgHom K A) = T := by
    apply Matrix.ext
    intro i j
    apply Unitization.ext
    · have hentry : (T i j).fst = 0 := congrFun (congrFun hT i) j
      change (0 : K) = (T i j).fst
      exact hentry.symm
    · rfl
  obtain ⟨e, he⟩ := matrixNil M
  refine ⟨e + 1, ?_⟩
  rw [← positivePower_eq_pow]
  rw [← hM, ← unitization_map_positivePower, he]
  apply Matrix.ext
  intro i j
  change ((0 : A) : Unitization K A) = 0
  exact Unitization.inr_zero K

/-- Every matrix over the unitization is algebraic if the corresponding
non-unital matrix algebra is nil. -/
theorem unitization_matrix_isAlgebraic
    (matrixNil : ∀ M : Matrix n n A, ∃ e : ℕ, positivePower M e = 0)
    (T : Matrix n n (Unitization K A)) : IsAlgebraic K T := by
  apply isAlgebraic_of_matrix_quotient_nil_kernel
    (Unitization.fstHom K A).mapMatrix
    (unitization_matrix_kernel_nil matrixNil)

/-- The whole actual matrix algebra over the unitization is algebraic. -/
theorem unitization_matrix_algebraic
    (matrixNil : ∀ M : Matrix n n A, ∃ e : ℕ, positivePower M e = 0) :
    Algebra.IsAlgebraic K (Matrix n n (Unitization K A)) := by
  exact ⟨unitization_matrix_isAlgebraic matrixNil⟩

end Unitization

section AllMatrixOrders

variable {K A : Type*} [Field K] [NonUnitalRing A] [Module K A]
  [IsScalarTower K A A] [SMulCommClass K A A]

/-- If every finite matrix over a non-unital algebra `A` is nilpotent, every
finite matrix over its unitization is algebraic over the field `K`.
The statement includes matrices of order zero. -/
theorem all_unitization_matrices_isAlgebraic
    (matrixNil : ∀ r : ℕ, ∀ M : Matrix (Fin r) (Fin r) A,
      ∃ e : ℕ, positivePower M e = 0) :
    ∀ r : ℕ, ∀ T : Matrix (Fin r) (Fin r) (Unitization K A),
      IsAlgebraic K T := by
  intro r T
  exact unitization_matrix_isAlgebraic (matrixNil r) T

/-- Algebraicity of all matrix orders, expressed using Mathlib's
`Algebra.IsAlgebraic` class. -/
theorem all_unitization_matrix_algebras_algebraic
    (matrixNil : ∀ r : ℕ, ∀ M : Matrix (Fin r) (Fin r) A,
      ∃ e : ℕ, positivePower M e = 0) :
    ∀ r : ℕ, Algebra.IsAlgebraic K (Matrix (Fin r) (Fin r) (Unitization K A)) := by
  intro r
  exact unitization_matrix_algebraic (matrixNil r)

end AllMatrixOrders

end CriticalGK2
