import CriticalGK2.TensorCutRank

/-! # Thin composed interfaces for actual fixed-factor cut rank transport -/

namespace CriticalGK2.ContractionBudget

noncomputable section

open TensorProduct

variable {F X Y Z A : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]
  [AddCommGroup Z] [Module F Z]
  [AddCommGroup A] [Module F A]

theorem tensorCutRank_append_transport (e : Y ⊗[F] Z ≃ₗ[F] A)
    (t : X ⊗[F] Y) (z : Z) (hz : z ≠ 0) :
    tensorCutRank (e.lTensor X (TensorProduct.assoc F X Y Z (t ⊗ₜ[F] z))) =
      tensorCutRank t :=
  (tensorCutRank_rightEquiv (F := F) (X := X) (Y := Y ⊗[F] Z) (A := A) e
    (TensorProduct.assoc F X Y Z (t ⊗ₜ[F] z))).trans
      (tensorCutRank_append (F := F) (X := X) (Y := Y) (Z := Z) t z hz)

theorem tensorCutRank_prepend_transport (e : Z ⊗[F] X ≃ₗ[F] A)
    (z : Z) (hz : z ≠ 0) (t : X ⊗[F] Y) :
    tensorCutRank (e.rTensor Y ((TensorProduct.assoc F Z X Y).symm (z ⊗ₜ[F] t))) =
      tensorCutRank t :=
  (tensorCutRank_leftEquiv (F := F) (X := Z ⊗[F] X) (Y := Y) (A := A) e
    ((TensorProduct.assoc F Z X Y).symm (z ⊗ₜ[F] t))).trans
      (tensorCutRank_prepend (F := F) (X := X) (Y := Y) (Z := Z) z hz t)

end

end CriticalGK2.ContractionBudget
