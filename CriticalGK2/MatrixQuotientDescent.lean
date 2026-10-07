import CriticalGK2.PositiveQuotient
import CriticalGK2.Unitization
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Actual matrix descent from the positive free algebra to A

Every finite matrix over the actual non-unital A has an actual H-valued lift
whose entries have zero augmentation and a finite common positive degree range.
The actual quotient map and actual subtype inclusion preserve matrix positive
powers.  Therefore entrywise containment of a lifted positive power in the
actual all-cut E implies zero for the corresponding actual A-matrix power.

The descent theorem takes power absorption in E as its hypothesis.
For the sparse construction, the all-cut readback theorem supplies this
absorption.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- Actual inclusion of the non-unital positive algebra A into the unital B. -/
def positiveQuotientInclusion (W : DyadicDualData F) (hW : PrimalCoherent F W) :
    PositiveAllCutQuotient F W hW →ₙₐ[F] AllCutRingQuotient F W hW :=
  NonUnitalSubalgebraClass.subtype (positiveAllCutSubalgebra F W hW)

@[simp]
theorem positiveQuotientInclusion_apply (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (x : PositiveAllCutQuotient F W hW) :
    positiveQuotientInclusion F W hW x = x.val := rfl

theorem wordQuotientMap_matrix_positivePower (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (r : ℕ)
    (M : Matrix (Fin r) (Fin r) (WordAlgebra F)) (e : ℕ) :
    (positivePower M e).map (allCutQuotientMap F W hW) =
      positivePower (M.map (allCutQuotientMap F W hW)) e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [positivePower, Matrix.map_mul, ih]
      rfl

theorem positiveQuotientInclusion_matrix_positivePower (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (r : ℕ)
    (M : Matrix (Fin r) (Fin r) (PositiveAllCutQuotient F W hW)) (e : ℕ) :
    (positivePower M e).map (positiveQuotientInclusion F W hW) =
      positivePower (M.map (positiveQuotientInclusion F W hW)) e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [positivePower, Matrix.map_mul, ih]
      rfl

/-- Entrywise actual lifts exist and each lifted entry is in H_+. -/
theorem exists_positive_wordMatrix_lift (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (r : ℕ)
    (M : Matrix (Fin r) (Fin r) (PositiveAllCutQuotient F W hW)) :
    ∃ L : Matrix (Fin r) (Fin r) (WordAlgebra F),
      (∀ i j, augmentation F (L i j) = 0) ∧
      L.map (allCutQuotientMap F W hW) =
        M.map (positiveQuotientInclusion F W hW) := by
  classical
  let a : Fin r → Fin r → positiveWordSubmodule F := fun i j =>
    Classical.choose (positiveAllCutQuotientMap_surjective F W hW (M i j))
  have ha : ∀ i j, positiveAllCutQuotientMap F W hW (a i j) = M i j := fun i j =>
    Classical.choose_spec (positiveAllCutQuotientMap_surjective F W hW (M i j))
  let L : Matrix (Fin r) (Fin r) (WordAlgebra F) := fun i j => (a i j).val
  refine ⟨L, ?_, ?_⟩
  · intro i j
    exact (a i j).property
  · apply Matrix.ext
    intro i j
    change allCutQuotientMap F W hW (a i j).val = (M i j).val
    exact congrArg (fun x : PositiveAllCutQuotient F W hW => x.val) (ha i j)

/-- A finite common degree bound, computed from all actual entry supports. -/
def wordMatrixDegreeBound (r : ℕ) (M : Matrix (Fin r) (Fin r) (WordAlgebra F)) : ℕ := by
  classical
  exact Finset.univ.sup (fun p : Fin r × Fin r =>
    (MonoidAlgebra.coeff (M p.1 p.2)).support.sup (fun w : Word => w.length))

theorem wordMatrixEntry_degree_le (r : ℕ)
    (M : Matrix (Fin r) (Fin r) (WordAlgebra F))
    (i j : Fin r) (w : Word) (hw : (M i j) w ≠ 0) :
    w.length ≤ wordMatrixDegreeBound F r M := by
  classical
  have hwmem : w ∈ (MonoidAlgebra.coeff (M i j)).support :=
    Finsupp.mem_support_iff.mpr hw
  have hlocal : w.length ≤
      (MonoidAlgebra.coeff (M i j)).support.sup (fun w : Word => w.length) :=
    Finset.le_sup hwmem
  have hall : (MonoidAlgebra.coeff (M i j)).support.sup (fun w : Word => w.length) ≤
      wordMatrixDegreeBound F r M := by
    change (MonoidAlgebra.coeff (M i j)).support.sup (fun w : Word => w.length) ≤
      Finset.univ.sup (fun p : Fin r × Fin r =>
        (MonoidAlgebra.coeff (M p.1 p.2)).support.sup (fun w : Word => w.length))
    exact Finset.le_sup (f := fun p : Fin r × Fin r =>
      (MonoidAlgebra.coeff (M p.1 p.2)).support.sup (fun w : Word => w.length))
      (Finset.mem_univ (i, j))
  exact hlocal.trans hall

/-- Zero augmentation excludes degree zero, and finite supports bound all others. -/
theorem exists_positive_wordMatrix_degree_range (r : ℕ)
    (M : Matrix (Fin r) (Fin r) (WordAlgebra F))
    (hM : ∀ i j, augmentation F (M i j) = 0) :
    ∃ d : ℕ, 0 < d ∧ ∀ i j w, (M i j) w ≠ 0 →
      1 ≤ w.length ∧ w.length ≤ d := by
  refine ⟨wordMatrixDegreeBound F r M + 1, by omega, ?_⟩
  intro i j w hw
  have hpositive : w.length ≠ 0 := by
    intro hz
    have hwone : w = 1 := FreeMonoid.length_eq_zero.mp hz
    subst w
    apply hw
    rw [← augmentation_eq_constantCoeff F (M i j)]
    exact hM i j
  have hupper := wordMatrixEntry_degree_le F r M i j w hw
  constructor <;> omega

/-- A lifted power lying entrywise in the actual E gives zero in actual A. -/
theorem positiveMatrixPower_eq_zero_of_lift (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (r : ℕ)
    (M : Matrix (Fin r) (Fin r) (PositiveAllCutQuotient F W hW))
    (L : Matrix (Fin r) (Fin r) (WordAlgebra F))
    (hmap : L.map (allCutQuotientMap F W hW) =
      M.map (positiveQuotientInclusion F W hW))
    (e : ℕ) (hE : ∀ i j, (positivePower L e) i j ∈ allCutSubmodule F W) :
    positivePower M e = 0 := by
  have hzero : (positivePower L e).map (allCutQuotientMap F W hW) = 0 := by
    apply Matrix.ext
    intro i j
    exact (allCutQuotientMap_eq_zero_iff F W hW ((positivePower L e) i j)).mpr (hE i j)
  have hA : (positivePower M e).map (positiveQuotientInclusion F W hW) = 0 := by
    rw [positiveQuotientInclusion_matrix_positivePower, ← hmap,
      ← wordQuotientMap_matrix_positivePower, hzero]
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  exact congrFun (congrFun hA i) j

/-- Conditional descent with the exact remaining free-algebra power absorption
obligation written explicitly. -/
theorem matrixNil_of_wordMatrix_power_absorption (W : DyadicDualData F)
    (hW : PrimalCoherent F W)
    (powerAbsorption : ∀ r : ℕ,
      ∀ L : Matrix (Fin r) (Fin r) (WordAlgebra F),
      (∀ i j, augmentation F (L i j) = 0) →
      ∃ e : ℕ, ∀ i j, (positivePower L e) i j ∈ allCutSubmodule F W) :
    ∀ r : ℕ, ∀ M : Matrix (Fin r) (Fin r) (PositiveAllCutQuotient F W hW),
      ∃ e : ℕ, positivePower M e = 0 := by
  intro r M
  obtain ⟨L, hL, hmap⟩ := exists_positive_wordMatrix_lift F W hW r M
  obtain ⟨e, hE⟩ := powerAbsorption r L hL
  exact ⟨e, positiveMatrixPower_eq_zero_of_lift F W hW r M L hmap e hE⟩

/-- The same actual descent, indexed by matrix order and a finite positive
degree range, as required by the sparse operation schedule. -/
theorem matrixNil_of_bounded_wordMatrix_power_absorption (W : DyadicDualData F)
    (hW : PrimalCoherent F W)
    (powerAbsorption : ∀ r d : ℕ, 0 < d →
      ∀ L : Matrix (Fin r) (Fin r) (WordAlgebra F),
      (∀ i j w, (L i j) w ≠ 0 → 1 ≤ w.length ∧ w.length ≤ d) →
      ∃ e : ℕ, ∀ i j, (positivePower L e) i j ∈ allCutSubmodule F W) :
    ∀ r : ℕ, ∀ M : Matrix (Fin r) (Fin r) (PositiveAllCutQuotient F W hW),
      ∃ e : ℕ, positivePower M e = 0 := by
  intro r M
  obtain ⟨L, hL, hmap⟩ := exists_positive_wordMatrix_lift F W hW r M
  obtain ⟨d, hd, hdegree⟩ := exists_positive_wordMatrix_degree_range F r L hL
  obtain ⟨e, hE⟩ := powerAbsorption r d hd L hdegree
  exact ⟨e, positiveMatrixPower_eq_zero_of_lift F W hW r M L hmap e hE⟩

end

end CriticalGK2.Actual
