import CriticalGK2.TensorCutDuality
import CriticalGK2.DyadicDegreeCast

/-!
# Literal homogeneous cut tensors and the actual all-cut annihilator formula

The tensor relation is transported by the actual word-concatenation equivalence,
and its image is proved to equal the actual cut sum restricted to H_n.  The
actual tensor-dual formula is then transported by that same equivalence, with
the literal equality i + (n-i) = n accounted for on both primal and dual sides.
-/

namespace CriticalGK2.Actual

open TensorProduct

noncomputable section

variable (F : Type*) [Field F]

theorem homogeneousCutDegree (n : ℕ) (i : Fin (n + 1)) : i.val + (n - i.val) = n :=
  Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)

/-- Actual concatenation into the literal H_n cut ambient. -/
def homogeneousTensorCutConcat {a b n : ℕ} (hab : a + b = n) :
    homogeneous F a ⊗[F] homogeneous F b ≃ₗ[F] homogeneous F n :=
  (homogeneousTensorConcat F a b).trans (homogeneousDegreeCast F hab)

/-- The corresponding actual dual concatenation into H_n^*. -/
def homogeneousDualTensorCutConcat {a b n : ℕ} (hab : a + b = n) :
    HomogeneousDual F a ⊗[F] HomogeneousDual F b ≃ₗ[F] HomogeneousDual F n :=
  (homogeneousDualTensorConcat F a b).trans (homogeneousDualDegreeCast F hab)

@[simp]
theorem homogeneousTensorCutConcat_tmul_val {a b n : ℕ} (hab : a + b = n)
    (x : homogeneous F a) (y : homogeneous F b) :
    (homogeneousTensorCutConcat F hab (x ⊗ₜ[F] y)).val = x.val * y.val := by
  rw [homogeneousTensorCutConcat, LinearEquiv.trans_apply, homogeneousDegreeCast_coe,
    homogeneousTensorConcat_tmul_coe]

theorem homogeneousTensorCutConcat_dualDistrib {a b n : ℕ} (hab : a + b = n) :
    (homogeneousTensorCutConcat F hab).symm.dualMap.toLinearMap.comp
        (TensorProduct.dualDistrib F (homogeneous F a) (homogeneous F b)) =
      (homogeneousDualTensorCutConcat F hab).toLinearMap := by
  subst n
  rfl

/-- Transport of annihilators along an actual linear equivalence. -/
theorem dualAnnihilator_map_equiv
    {X Y : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (S : Submodule F X) (e : X ≃ₗ[F] Y) :
    (S.map e.toLinearMap).dualAnnihilator = S.dualAnnihilator.map e.symm.dualMap.toLinearMap := by
  apply Submodule.ext
  intro φ
  constructor
  · intro hφ
    have hθ : φ.comp e.toLinearMap ∈ S.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      exact (Submodule.mem_dualAnnihilator φ).mp hφ _
        (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
    refine Submodule.mem_map.mpr ⟨φ.comp e.toLinearMap, hθ, ?_⟩
    apply LinearMap.ext
    intro y
    change φ (e (e.symm y)) = φ y
    rw [LinearEquiv.apply_symm_apply]
  · rintro ⟨θ, hθ, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    change θ (e.symm (e x)) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact (Submodule.mem_dualAnnihilator θ).mp hθ x hx

/-- The two actual tensor relation factors, concatenated into H_n, give exactly
the actual cut space including both endpoint cases. -/
theorem homogeneousCutSpace_eq_tensorCutRelation_map (W : DyadicDualData F)
    (n : ℕ) (i : Fin (n + 1)) :
    homogeneousCutSpace F W n i =
      (tensorCutRelation F (homogeneousLeftCompletion F W i.val)
        (homogeneousRightCompletion F W (n - i.val))).map
          (homogeneousTensorCutConcat F (homogeneousCutDegree n i)).toLinearMap := by
  let D := homogeneousLeftCompletion F W i.val
  let G := homogeneousRightCompletion F W (n - i.val)
  let e := homogeneousTensorCutConcat F (homogeneousCutDegree n i)
  let S := tensorCutRelation F D G
  let T := S.map e.toLinearMap
  have hfirst : ∀ z : D ⊗[F] homogeneous F (n - i.val),
      (e (TensorProduct.map D.subtype (LinearMap.id : homogeneous F (n - i.val) →ₗ[F] _)
        z)).val ∈ productSpan F (leftCompletion F W i.val) (homogeneous F (n - i.val)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [LinearMap.map_zero, LinearEquiv.map_zero]
        exact (productSpan F (leftCompletion F W i.val)
          (homogeneous F (n - i.val))).zero_mem
    | add z z' hz hz' =>
        simpa only [map_add] using
          (productSpan F (leftCompletion F W i.val) (homogeneous F (n - i.val))).add_mem hz hz'
    | tmul x y =>
        simp only [TensorProduct.map_tmul, LinearMap.id_apply]
        rw [homogeneousTensorCutConcat_tmul_val]
        exact mul_mem_productSpan F x.property y.property
  have hsecond : ∀ z : homogeneous F i.val ⊗[F] G,
      (e (TensorProduct.map (LinearMap.id : homogeneous F i.val →ₗ[F] _)
        G.subtype z)).val ∈
        productSpan F (homogeneous F i.val) (rightCompletion F W (n - i.val)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [LinearMap.map_zero, LinearEquiv.map_zero]
        exact (productSpan F (homogeneous F i.val)
          (rightCompletion F W (n - i.val))).zero_mem
    | add z z' hz hz' =>
        simpa only [map_add] using
          (productSpan F (homogeneous F i.val) (rightCompletion F W (n - i.val))).add_mem hz hz'
    | tmul x y =>
        simp only [TensorProduct.map_tmul, LinearMap.id_apply]
        rw [homogeneousTensorCutConcat_tmul_val]
        exact mul_mem_productSpan F x.property y.property
  have hforward : T ≤ homogeneousCutSpace F W n i := by
    rw [Submodule.map_le_iff_le_comap]
    apply sup_le
    · intro z hz
      obtain ⟨u, rfl⟩ := hz
      exact Submodule.mem_sup_left (hfirst u)
    · intro z hz
      obtain ⟨u, rfl⟩ := hz
      exact Submodule.mem_sup_right (hsecond u)
  have hfirstback : productSpan F (leftCompletion F W i.val) (homogeneous F (n - i.val)) ≤
      T.map (homogeneous F n).subtype := by
    rw [productSpan_le_iff]
    intro x hx y hy
    let xH : homogeneous F i.val := ⟨x, leftCompletion_le_homogeneous F W i.val hx⟩
    let xD : D := ⟨xH, hx⟩
    let yH : homogeneous F (n - i.val) := ⟨y, hy⟩
    let z := TensorProduct.map D.subtype (LinearMap.id : homogeneous F (n - i.val) →ₗ[F] _)
      (xD ⊗ₜ[F] yH)
    have hz : z ∈ S := Submodule.mem_sup_left ⟨xD ⊗ₜ[F] yH, rfl⟩
    refine Submodule.mem_map.mpr ⟨e z, Submodule.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
    change (e z).val = x * y
    simp only [z, TensorProduct.map_tmul, LinearMap.id_apply]
    exact homogeneousTensorCutConcat_tmul_val F (homogeneousCutDegree n i) xH yH
  have hsecondback : productSpan F (homogeneous F i.val) (rightCompletion F W (n - i.val)) ≤
      T.map (homogeneous F n).subtype := by
    rw [productSpan_le_iff]
    intro x hx y hy
    let xH : homogeneous F i.val := ⟨x, hx⟩
    let yH : homogeneous F (n - i.val) :=
      ⟨y, rightCompletion_le_homogeneous F W (n - i.val) hy⟩
    let yG : G := ⟨yH, hy⟩
    let z := TensorProduct.map (LinearMap.id : homogeneous F i.val →ₗ[F] _) G.subtype
      (xH ⊗ₜ[F] yG)
    have hz : z ∈ S := Submodule.mem_sup_right ⟨xH ⊗ₜ[F] yG, rfl⟩
    refine Submodule.mem_map.mpr ⟨e z, Submodule.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
    change (e z).val = x * y
    simp only [z, TensorProduct.map_tmul, LinearMap.id_apply]
    exact homogeneousTensorCutConcat_tmul_val F (homogeneousCutDegree n i) xH yH
  apply le_antisymm
  · intro x hx
    have hx' := (sup_le hfirstback hsecondback) hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx'
    have hyx' : y = x := Subtype.ext hyx
    simpa only [hyx'] using hy
  · exact hforward

/-- Literal actual dual tensor product at a cut, transported into H_n^*. -/
def homogeneousCutDualTensorProduct (W : DyadicDualData F) (n : ℕ) (i : Fin (n + 1)) :
    Submodule F (HomogeneousDual F n) :=
  (actualDualTensorProduct F i.val (n - i.val)
    (homogeneousLeftCompletion F W i.val).dualAnnihilator
    (homogeneousRightCompletion F W (n - i.val)).dualAnnihilator).map
      (homogeneousDualDegreeCast F (homogeneousCutDegree n i)).toLinearMap

/-- The exact cut annihilator is the literal actual concatenated dual tensor product. -/
theorem homogeneousCutSpace_dualAnnihilator (W : DyadicDualData F)
    (n : ℕ) (i : Fin (n + 1)) :
    (homogeneousCutSpace F W n i).dualAnnihilator =
      homogeneousCutDualTensorProduct F W n i := by
  rw [homogeneousCutSpace_eq_tensorCutRelation_map]
  calc
    _ = (tensorCutRelation F (homogeneousLeftCompletion F W i.val)
        (homogeneousRightCompletion F W (n - i.val))).dualAnnihilator.map
          (homogeneousTensorCutConcat F (homogeneousCutDegree n i)).symm.dualMap.toLinearMap :=
      dualAnnihilator_map_equiv F
        (tensorCutRelation F (homogeneousLeftCompletion F W i.val)
          (homogeneousRightCompletion F W (n - i.val)))
        (homogeneousTensorCutConcat F (homogeneousCutDegree n i))
    _ = _ := by
      rw [tensorCutRelation_dualAnnihilator, ← Submodule.map_comp,
        homogeneousTensorCutConcat_dualDistrib]
      simp only [homogeneousCutDualTensorProduct, actualDualTensorProduct,
        ← Submodule.map_comp, homogeneousDualTensorCutConcat]
      all_goals rfl

/-- The manuscript's actual all-cut annihilator decomposition, including both
endpoint scalar factors, with every degree transport made explicit. -/
theorem homogeneousAllCutComponent_dualAnnihilator_eq_actualTensorCuts
    (W : DyadicDualData F) (n : ℕ) :
    (homogeneousAllCutComponent F W n).dualAnnihilator =
      ⨆ i : Fin (n + 1), homogeneousCutDualTensorProduct F W n i := by
  rw [homogeneousAllCutComponent_dualAnnihilator]
  congr 1
  funext i
  exact homogeneousCutSpace_dualAnnihilator F W n i

end

end CriticalGK2.Actual
