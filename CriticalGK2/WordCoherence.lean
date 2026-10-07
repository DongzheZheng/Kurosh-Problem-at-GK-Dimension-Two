import CriticalGK2.WordTensor

/-!
# Actual dual coherence implies actual primal multiplication coherence

The dual tensor subspace is constructed by tensorizing actual inclusions and
then using the proved actual dual concatenation equivalence.  Its annihilator
law follows by tensor induction and the product pairing.
-/

namespace CriticalGK2.Actual

open TensorProduct

variable (F : Type*) [Field F]

/-- The actual dual tensor-product subspace, included in the actual
homogeneous degree-(a+b) dual space. -/
noncomputable def actualDualTensorProduct (a b : ℕ)
    (W₁ : Submodule F (HomogeneousDual F a))
    (W₂ : Submodule F (HomogeneousDual F b)) :
    Submodule F (HomogeneousDual F (a + b)) :=
  (LinearMap.range (TensorProduct.map W₁.subtype W₂.subtype)).map
    (homogeneousDualTensorConcat F a b).toLinearMap

/-- Actual pairings vanish when the first primal factor annihilates the
complete first dual block. -/
theorem actualDualTensorProduct_pairing_zero_left (a b : ℕ)
    (W₁ : Submodule F (HomogeneousDual F a))
    (W₂ : Submodule F (HomogeneousDual F b))
    (x : homogeneous F a) (hx : x ∈ W₁.dualCoannihilator)
    (y : homogeneous F b) (θ : HomogeneousDual F (a + b))
    (hθ : θ ∈ actualDualTensorProduct F a b W₁ W₂) :
    θ (homogeneousMultiplication F a b x y) = 0 := by
  obtain ⟨z, ⟨w, rfl⟩, rfl⟩ := hθ
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv =>
    simp only [map_add, LinearMap.add_apply, hu, hv, add_zero]
  | tmul φ ψ =>
    simp only [TensorProduct.map_tmul]
    rw [← homogeneousTensorConcat_tmul F a b x y]
    have hφ : (φ : HomogeneousDual F a) x = 0 :=
      (Submodule.mem_dualCoannihilator x).mp hx φ φ.property
    exact (homogeneousDualTensorConcat_pairing F a b φ.val ψ.val x y).trans
      (by rw [hφ, zero_mul])

/-- The mirror pairing law for an annihilating last primal factor. -/
theorem actualDualTensorProduct_pairing_zero_right (a b : ℕ)
    (W₁ : Submodule F (HomogeneousDual F a))
    (W₂ : Submodule F (HomogeneousDual F b))
    (x : homogeneous F a)
    (y : homogeneous F b) (hy : y ∈ W₂.dualCoannihilator)
    (θ : HomogeneousDual F (a + b))
    (hθ : θ ∈ actualDualTensorProduct F a b W₁ W₂) :
    θ (homogeneousMultiplication F a b x y) = 0 := by
  obtain ⟨z, ⟨w, rfl⟩, rfl⟩ := hθ
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv =>
    simp only [map_add, LinearMap.add_apply, hu, hv, add_zero]
  | tmul φ ψ =>
    simp only [TensorProduct.map_tmul]
    rw [← homogeneousTensorConcat_tmul F a b x y]
    have hψ : (ψ : HomogeneousDual F b) y = 0 :=
      (Submodule.mem_dualCoannihilator y).mp hy ψ ψ.property
    exact (homogeneousDualTensorConcat_pairing F a b φ.val ψ.val x y).trans
      (by rw [hψ, mul_zero])

/-- Actual dual coherence forces the left primal multiplication inclusion.
This is the first half of `U_h H_(2^h) + H_(2^h) U_h ⊆ U_(h+1)`. -/
theorem homogeneousMultiplication_mem_dualCoannihilator_left (a b : ℕ)
    (W₁ : Submodule F (HomogeneousDual F a))
    (W₂ : Submodule F (HomogeneousDual F b))
    (next : Submodule F (HomogeneousDual F (a + b)))
    (hnext : next ≤ actualDualTensorProduct F a b W₁ W₂)
    (x : homogeneous F a) (y : homogeneous F b)
    (hx : x ∈ W₁.dualCoannihilator) :
    homogeneousMultiplication F a b x y ∈ next.dualCoannihilator := by
  rw [Submodule.mem_dualCoannihilator]
  intro θ hθ
  exact actualDualTensorProduct_pairing_zero_left F a b W₁ W₂ x hx y θ (hnext hθ)

/-- Actual dual coherence forces the right primal multiplication inclusion. -/
theorem homogeneousMultiplication_mem_dualCoannihilator_right (a b : ℕ)
    (W₁ : Submodule F (HomogeneousDual F a))
    (W₂ : Submodule F (HomogeneousDual F b))
    (next : Submodule F (HomogeneousDual F (a + b)))
    (hnext : next ≤ actualDualTensorProduct F a b W₁ W₂)
    (x : homogeneous F a)
    (y : homogeneous F b) (hy : y ∈ W₂.dualCoannihilator) :
    homogeneousMultiplication F a b x y ∈ next.dualCoannihilator := by
  rw [Submodule.mem_dualCoannihilator]
  intro θ hθ
  exact actualDualTensorProduct_pairing_zero_right F a b W₁ W₂ x y hy θ (hnext hθ)

end CriticalGK2.Actual
