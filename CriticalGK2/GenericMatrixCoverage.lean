import CriticalGK2.GenericMatrixCoefficients

/-!
# Actual positive free-word matrix coverage

Every matrix of actual positive noncommutative polynomials over any
commutative coefficient ring is an instance of the actual generic matrix.
The coefficients are read from the matrix itself.  A common degree bound is
constructed from its finite word support.
-/

namespace CriticalGK2.Automaton

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R] {r d : ℕ}

/-- Exact first-letter and residual comparison in the original free monoid. -/
theorem ofList_cons_eq_iff (α β : Bool) (p w : List Bool) :
    FreeMonoid.ofList (β :: p) = FreeMonoid.ofList (α :: w) ↔ β = α ∧ p = w := by
  constructor
  · intro h
    exact List.cons.inj (congrArg FreeMonoid.toList h)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Exact actual coefficients of a nonempty generic-entry word. -/
theorem genericEntry_cons_coefficient (c : Coefficients R r d)
    (α : Bool) (w : List Bool) (a b : Fin r) :
    genericEntry c a b (FreeMonoid.ofList (α :: w)) =
      ∑ p : Residual d, if p.val = w then c a b α p else 0 := by
  classical
  rw [genericEntry, wordCoefficient_sum]
  simp_rw [wordCoefficient_sum, MonoidAlgebra.single_apply, ofList_cons_eq_iff]
  cases α <;> simp

/-- Positive generic entries have zero actual augmentation. -/
theorem genericEntry_nil_coefficient (c : Coefficients R r d) (a b : Fin r) :
    genericEntry c a b (FreeMonoid.ofList []) = 0 := by
  have h := genericEntry_mul_nil_coefficient c a b (1 : MonoidAlgebra R (FreeMonoid Bool))
  simpa only [mul_one] using h

/-- Every allowed word appears exactly once in the generic entry. -/
theorem genericEntry_cons_coefficient_of_short (c : Coefficients R r d)
    (α : Bool) (w : List Bool) (a b : Fin r) (hw : w.length < d) :
    genericEntry c a b (FreeMonoid.ofList (α :: w)) = c a b α ⟨w, hw⟩ := by
  classical
  rw [genericEntry_cons_coefficient]
  let p₀ : Residual d := ⟨w, hw⟩
  have heq (p : Residual d) : p.val = w ↔ p = p₀ := by
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      subst p
      rfl
  simp_rw [heq]
  simp [p₀]

/-- Words beyond the stated degree window have zero generic-entry coefficient. -/
theorem genericEntry_cons_coefficient_of_long (c : Coefficients R r d)
    (α : Bool) (w : List Bool) (a b : Fin r) (hw : d ≤ w.length) :
    genericEntry c a b (FreeMonoid.ofList (α :: w)) = 0 := by
  classical
  rw [genericEntry_cons_coefficient]
  apply Finset.sum_eq_zero
  intro p _
  have hne : p.val ≠ w := by
    intro h
    have hp := p.property
    rw [h] at hp
    omega
  simp [hne]

/-- The actual generic coefficients of an actual matrix, obtained by coefficient reading. -/
def coefficientsFromMatrix
    (M : Matrix (Fin r) (Fin r) (MonoidAlgebra R (FreeMonoid Bool))) :
    Coefficients R r d :=
  fun a b α p => M a b (FreeMonoid.ofList (α :: p.val))

/-- Exact generic representation of a positive matrix with a common degree bound. -/
theorem genericMatrix_coefficientsFromMatrix
    (M : Matrix (Fin r) (Fin r) (MonoidAlgebra R (FreeMonoid Bool)))
    (hpositive : ∀ a b, M a b 1 = 0)
    (hdegree : ∀ a b w, d < w.length → M a b w = 0) :
    genericMatrix (coefficientsFromMatrix (d := d) M) = M := by
  classical
  funext a b
  apply Finsupp.ext
  intro w
  have hcoeff : ∀ l : List Bool,
      genericEntry (coefficientsFromMatrix (d := d) M) a b (FreeMonoid.ofList l) =
        M a b (FreeMonoid.ofList l) := by
    intro l
    cases l with
    | nil =>
        simpa only [FreeMonoid.ofList_nil] using
          ((genericEntry_nil_coefficient (coefficientsFromMatrix (d := d) M) a b).trans
            ((hpositive a b).symm))
    | cons α p =>
      by_cases hp : p.length < d
      · rw [genericEntry_cons_coefficient_of_short _ α p a b hp]
        rfl
      · rw [genericEntry_cons_coefficient_of_long _ α p a b (by omega)]
        apply (hdegree a b (FreeMonoid.ofList (α :: p)) ?_).symm
        change d < (α :: p).length
        simp only [List.length_cons]
        omega
  simpa only [FreeMonoid.ofList_toList] using hcoeff w.toList

/-- The actual finite word support of all matrix entries together. -/
def matrixWordSupport
    (M : Matrix (Fin r) (Fin r) (MonoidAlgebra R (FreeMonoid Bool))) :
    Finset (FreeMonoid Bool) := by
  classical
  exact Finset.univ.biUnion fun a => Finset.univ.biUnion fun b => (M a b).support

/-- An explicit positive common bound from the finite actual matrix support. -/
def matrixDegreeBound
    (M : Matrix (Fin r) (Fin r) (MonoidAlgebra R (FreeMonoid Bool))) : ℕ :=
  (matrixWordSupport M).sup FreeMonoid.length + 1

theorem matrixDegreeBound_pos
    (M : Matrix (Fin r) (Fin r) (MonoidAlgebra R (FreeMonoid Bool))) :
    0 < matrixDegreeBound M := by
  unfold matrixDegreeBound
  omega

/-- No actual entry coefficient lies beyond the support-derived bound. -/
theorem matrix_coefficient_zero_of_degreeBound_lt
    (M : Matrix (Fin r) (Fin r) (MonoidAlgebra R (FreeMonoid Bool)))
    (a b : Fin r) (w : FreeMonoid Bool) (hw : matrixDegreeBound M < w.length) :
    M a b w = 0 := by
  classical
  by_contra hne
  have hmem : w ∈ matrixWordSupport M := by
    simp only [matrixWordSupport, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨a, b, Finsupp.mem_support_iff.mpr hne⟩
  have hle : w.length ≤ (matrixWordSupport M).sup FreeMonoid.length := Finset.le_sup hmem
  unfold matrixDegreeBound at hw
  omega

/-- Every actual positive free-word matrix is a generic instance, including
its explicit actual coefficient function and a positive finite degree bound. -/
theorem exists_genericMatrix_representation
    (M : Matrix (Fin r) (Fin r) (MonoidAlgebra R (FreeMonoid Bool)))
    (hpositive : ∀ a b, M a b 1 = 0) :
    ∃ (d : ℕ) (_ : 0 < d) (c : Coefficients R r d), genericMatrix c = M := by
  refine ⟨matrixDegreeBound M, matrixDegreeBound_pos M,
    coefficientsFromMatrix (d := matrixDegreeBound M) M, ?_⟩
  exact genericMatrix_coefficientsFromMatrix M hpositive
    (matrix_coefficient_zero_of_degreeBound_lt M)

#print axioms CriticalGK2.Automaton.genericMatrix_coefficientsFromMatrix
#print axioms CriticalGK2.Automaton.exists_genericMatrix_representation

end

end CriticalGK2.Automaton
