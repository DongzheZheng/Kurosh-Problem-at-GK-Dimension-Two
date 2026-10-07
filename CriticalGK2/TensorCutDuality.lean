import CriticalGK2.CutDuality
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# The actual tensor cut quotient and its exact annihilator

The kernel of the actual tensor product of quotient maps is proved using the
actual tensor-quotient equivalence.  Dualizing this kernel and the actual dual
tensor distribution gives (D tensor Y + X tensor G)^perp = D^perp tensor G^perp.
This is the finite-dimensional tensor factor step needed at each actual cut.
-/

namespace CriticalGK2.Actual

open TensorProduct

noncomputable section

variable (F : Type*) [Field F]
variable {X Y : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]

/-- The actual sum of the two tensor relation subspaces. -/
def tensorCutRelation (D : Submodule F X) (G : Submodule F Y) :
    Submodule F (X ⊗[F] Y) :=
  LinearMap.range (TensorProduct.map D.subtype (LinearMap.id : Y →ₗ[F] Y)) ⊔
    LinearMap.range (TensorProduct.map (LinearMap.id : X →ₗ[F] X) G.subtype)

/-- The actual tensor quotient map has precisely the two cut relations as kernel. -/
theorem tensorQuotientMap_ker (D : Submodule F X) (G : Submodule F Y) :
    (TensorProduct.map D.mkQ G.mkQ).ker = tensorCutRelation F D G := by
  let e := TensorProduct.quotientTensorQuotientEquiv D G
  have hcomp : e.toLinearMap.comp (TensorProduct.map D.mkQ G.mkQ) =
      (tensorCutRelation F D G).mkQ := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul,
      Submodule.mkQ_apply, TensorProduct.quotientTensorQuotientEquiv_apply_tmul_mk_tmul_mk]
    rfl
  apply Submodule.ext
  intro z
  change TensorProduct.map D.mkQ G.mkQ z = 0 ↔ z ∈ tensorCutRelation F D G
  have hez : e (TensorProduct.map D.mkQ G.mkQ z) =
      (tensorCutRelation F D G).mkQ z := LinearMap.congr_fun hcomp z
  constructor
  · intro hz
    have hzq : (tensorCutRelation F D G).mkQ z = 0 :=
      hez.symm.trans (by rw [hz, map_zero]; rfl)
    exact (Submodule.Quotient.mk_eq_zero _).mp hzq
  · intro hz
    apply e.injective
    have hzq : (tensorCutRelation F D G).mkQ z = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hz
    exact hez.trans (hzq.trans (map_zero e).symm)

/-- Naturality of the actual dual tensor pairing for the two quotient maps. -/
theorem tensorQuotientMap_dualDistrib (D : Submodule F X) (G : Submodule F Y) :
    (TensorProduct.map D.mkQ G.mkQ).dualMap.comp
        (TensorProduct.dualDistrib F (X ⧸ D) (Y ⧸ G)) =
      (TensorProduct.dualDistrib F X Y).comp
        (TensorProduct.map D.mkQ.dualMap G.mkQ.dualMap) := by
  apply TensorProduct.ext'
  intro φ ψ
  apply TensorProduct.ext'
  intro x y
  change φ (D.mkQ x) * ψ (G.mkQ y) = φ (D.mkQ x) * ψ (G.mkQ y)
  rfl

/-- Exact finite-dimensional two-factor annihilator formula. -/
theorem tensorCutRelation_dualAnnihilator [FiniteDimensional F X] [FiniteDimensional F Y]
    (D : Submodule F X) (G : Submodule F Y) :
    (tensorCutRelation F D G).dualAnnihilator =
      (LinearMap.range (TensorProduct.map D.dualAnnihilator.subtype
        G.dualAnnihilator.subtype)).map (TensorProduct.dualDistrib F X Y) := by
  let q := TensorProduct.map D.mkQ G.mkQ
  let t := TensorProduct.dualDistrib F (X ⧸ D) (Y ⧸ G)
  have ht : LinearMap.range t = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    exact (TensorProduct.dualDistribEquiv F (X ⧸ D) (Y ⧸ G)).surjective
  have hrt : LinearMap.range (TensorProduct.map D.mkQ.dualMap G.mkQ.dualMap) =
      LinearMap.range (TensorProduct.map D.dualAnnihilator.subtype
        G.dualAnnihilator.subtype) := by
    simp only [TensorProduct.range_map, Submodule.range_dualMap_mkQ_eq,
      Submodule.range_subtype]
  calc
    (tensorCutRelation F D G).dualAnnihilator = LinearMap.range q.dualMap := by
      rw [← tensorQuotientMap_ker F D G]
      exact (LinearMap.range_dualMap_eq_dualAnnihilator_ker q).symm
    _ = LinearMap.range (q.dualMap.comp t) :=
      (LinearMap.range_comp_of_range_eq_top q.dualMap ht).symm
    _ = LinearMap.range ((TensorProduct.dualDistrib F X Y).comp
        (TensorProduct.map D.mkQ.dualMap G.mkQ.dualMap)) := by
      rw [tensorQuotientMap_dualDistrib]
    _ = (LinearMap.range (TensorProduct.map D.mkQ.dualMap G.mkQ.dualMap)).map
        (TensorProduct.dualDistrib F X Y) := LinearMap.range_comp _ _
    _ = (LinearMap.range (TensorProduct.map D.dualAnnihilator.subtype
        G.dualAnnihilator.subtype)).map (TensorProduct.dualDistrib F X Y) := by rw [hrt]

end

end CriticalGK2.Actual
