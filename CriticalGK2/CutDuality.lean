import CriticalGK2.PrimalCompletion
import CriticalGK2.WordCoherence
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Actual homogeneous cut spaces and their finite-intersection duality

All spaces here are submodules of the actual homogeneous word components,
and their duals are the actual `HomogeneousDual` spaces.  Restriction along the
homogeneous subtype removes the outer H_n intersection in the actual E_n
definition.  The finite family of all cuts then has the exact annihilator-sum
formula from ordinary vector-space duality.

The tensor factor identification relates the annihilator of
L_i H_(n-i) + H_i R_(n-i) to the concatenated tensor product of the
homogeneous annihilators of L_i and R_(n-i).
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- L_n as an actual subspace inside H_n. -/
def homogeneousLeftCompletion (W : DyadicDualData F) (n : ℕ) :
    Submodule F (homogeneous F n) :=
  (leftCompletion F W n).comap (homogeneous F n).subtype

/-- R_n as an actual subspace inside H_n. -/
def homogeneousRightCompletion (W : DyadicDualData F) (n : ℕ) :
    Submodule F (homogeneous F n) :=
  (rightCompletion F W n).comap (homogeneous F n).subtype

/-- The original cut sum, restricted to the actual H_n subtype. -/
def homogeneousCutSpace (W : DyadicDualData F) (n : ℕ) (i : Fin (n + 1)) :
    Submodule F (homogeneous F n) :=
  (productSpan F (leftCompletion F W i.val) (homogeneous F (n - i.val)) ⊔
    productSpan F (homogeneous F i.val) (rightCompletion F W (n - i.val))).comap
      (homogeneous F n).subtype

/-- The actual all-cut component as a subspace inside H_n. -/
def homogeneousAllCutComponent (W : DyadicDualData F) (n : ℕ) :
    Submodule F (homogeneous F n) :=
  (allCutComponent F W n).comap (homogeneous F n).subtype

/-- All cuts, including both endpoints, remain after passing to H_n. -/
theorem homogeneousAllCutComponent_eq_iInf (W : DyadicDualData F) (n : ℕ) :
    homogeneousAllCutComponent F W n = ⨅ i : Fin (n + 1), homogeneousCutSpace F W n i := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    rw [Submodule.mem_iInf]
    intro i
    exact (Submodule.mem_iInf _).mp hx.2 i
  · intro hx
    change x.val ∈ allCutComponent F W n
    refine ⟨x.property, ?_⟩
    exact (Submodule.mem_iInf (fun i : Fin (n + 1) =>
      productSpan F (leftCompletion F W i.val) (homogeneous F (n - i.val)) ⊔
        productSpan F (homogeneous F i.val) (rightCompletion F W (n - i.val)))).mpr
      (fun i => (Submodule.mem_iInf _).mp hx i)

/-- Exact annihilator sum over the actual finite family of cuts. -/
theorem homogeneousAllCutComponent_dualAnnihilator (W : DyadicDualData F) (n : ℕ) :
    (homogeneousAllCutComponent F W n).dualAnnihilator =
      ⨆ i : Fin (n + 1), (homogeneousCutSpace F W n i).dualAnnihilator := by
  rw [homogeneousAllCutComponent_eq_iInf]
  exact Subspace.dualAnnihilator_iInf_eq _

/-- Once each actual cut annihilator vanishes under an actual linear map,
the actual E_n annihilator vanishes under that map. -/
theorem homogeneousAllCutComponent_dualAnnihilator_le_ker
    {C : Type*} [AddCommGroup C] [Module F C]
    (W : DyadicDualData F) (n : ℕ) (evaluate : HomogeneousDual F n →ₗ[F] C)
    (hcuts : ∀ i : Fin (n + 1),
      (homogeneousCutSpace F W n i).dualAnnihilator ≤ evaluate.ker) :
    (homogeneousAllCutComponent F W n).dualAnnihilator ≤ evaluate.ker := by
  rw [homogeneousAllCutComponent_dualAnnihilator]
  exact iSup_le hcuts

end

end CriticalGK2.Actual
