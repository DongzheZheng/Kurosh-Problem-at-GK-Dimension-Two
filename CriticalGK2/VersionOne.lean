import CriticalGK2.Unitization

/-!
# Algebraicity of matrix unitizations

Over an arbitrary field, nilpotence of every positive-order matrix over a
non-unital algebra implies algebraicity of every positive-order matrix over
its unitization. The theorems use Mathlib's unitization and matrix algebra.
-/

namespace CriticalGK2.VersionOne

variable {K A : Type*} [Field K] [NonUnitalRing A] [Module K A]
  [IsScalarTower K A A] [SMulCommClass K A A]

/-- Algebraicity of matrix unitizations in every positive order. -/
theorem capstone
    (matrixNil : ∀ r : ℕ, 0 < r → ∀ M : Matrix (Fin r) (Fin r) A,
      ∃ e : ℕ, CriticalGK2.positivePower M e = 0) :
    ∀ r : ℕ, 0 < r →
      Algebra.IsAlgebraic K (Matrix (Fin r) (Fin r) (Unitization K A)) := by
  intro r hr
  exact CriticalGK2.unitization_matrix_algebraic (matrixNil r hr)

/-- Every matrix over the unitization is algebraic when all positive-order
matrices over the underlying algebra are nilpotent. -/
theorem capstone_pointwise
    (matrixNil : ∀ r : ℕ, 0 < r → ∀ M : Matrix (Fin r) (Fin r) A,
      ∃ e : ℕ, CriticalGK2.positivePower M e = 0)
    (r : ℕ) (hr : 0 < r)
    (Y : Matrix (Fin r) (Fin r) (Unitization K A)) : IsAlgebraic K Y := by
  exact CriticalGK2.unitization_matrix_isAlgebraic (matrixNil r hr) Y

end CriticalGK2.VersionOne
