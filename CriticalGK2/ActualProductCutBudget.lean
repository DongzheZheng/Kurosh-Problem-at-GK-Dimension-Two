import CriticalGK2.ActualSpaceCutBudget
import CriticalGK2.TensorFrontProductCutSupport

/-!
# Multiplicative all-cut budgets for actual word tensor products

Every physical cut lies in the first or the last actual block. In both cases
the actual inverse concatenation is related to the honest tensor product
support spaces, including a fully arbitrary functional on the discarded
whole factor. The four explicit dimension inequalities below account for
all cuts without a graph, word, or family classification assumption.
-/

namespace CriticalGK2.ContractionBudget

noncomputable section

open TensorProduct

variable {F X Y Z A : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]
  [AddCommGroup Z] [Module F Z]
  [AddCommGroup A] [Module F A]

theorem tensorTailProductSpace_rightEquiv_prefixSupport_finrank_le
    [FiniteDimensional F X] (e : Y ⊗[F] Z ≃ₗ[F] A)
    (S : Submodule F (X ⊗[F] Y)) (T : Submodule F Z) :
    Module.finrank F (tensorPrefixSupport
      ((tensorTailProductSpace S T).map (e.lTensor X).toLinearMap)) ≤
        Module.finrank F (tensorPrefixSupport S) := by
  rw [tensorPrefixSupport_rightEquiv]
  exact tensorTailProductSpace_prefixSupport_finrank_le S T

theorem tensorTailProductSpace_rightEquiv_suffixSupport_finrank_le
    [FiniteDimensional F Y] [FiniteDimensional F Z] (e : Y ⊗[F] Z ≃ₗ[F] A)
    (S : Submodule F (X ⊗[F] Y)) (T : Submodule F Z) :
    Module.finrank F (tensorSuffixSupport
      ((tensorTailProductSpace S T).map (e.lTensor X).toLinearMap)) ≤
        Module.finrank F (tensorSuffixSupport S) * Module.finrank F T := by
  rw [tensorSuffixSupport_rightEquiv, e.finrank_map_eq]
  exact tensorTailProductSpace_suffixSupport_finrank_le S T

end

end CriticalGK2.ContractionBudget

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct CriticalGK2.ContractionBudget

variable (F : Type*) [Field F]

theorem actualDualSpaceCutMap_apply (n a b : ℕ) (hab : a + b = n)
    (phi : HomogeneousDual F n) :
    actualDualSpaceCutMap F n a b hab phi =
      wordCutTensor F a b (homogeneousDualDegreeCast F hab.symm phi) := by
  change (homogeneousDualTensorConcat F a b).symm
    ((homogeneousDualDegreeCast F hab).symm phi) = _
  rw [← homogeneousDualDegreeCast_symm_eq F hab]
  rfl

theorem actualDualSpaceCut_self_add (a b : ℕ)
    (S : Submodule F (HomogeneousDual F (a + b))) :
    actualDualSpaceCut F (a + b) a b rfl S =
      S.map (homogeneousDualTensorConcat F a b).symm.toLinearMap := by
  rfl

def actualProductLeftCutSpace (a b c : ℕ)
    (S : Submodule F (HomogeneousDual F (a + b))) (T : Submodule F (HomogeneousDual F c)) :=
  actualDualSpaceCut F ((a + b) + c) a (b + c) (Nat.add_assoc a b c).symm
    (actualDualTensorProduct F (a + b) c S T)

theorem actualProductLeftCutSpace_le (a b c : ℕ)
    (S : Submodule F (HomogeneousDual F (a + b))) (T : Submodule F (HomogeneousDual F c)) :
    actualProductLeftCutSpace F a b c S T ≤
      (tensorTailProductSpace (S.map (homogeneousDualTensorConcat F a b).symm.toLinearMap) T).map
        ((homogeneousDualTensorConcat F b c).lTensor (HomogeneousDual F a)).toLinearMap := by
  let B : Submodule F (HomogeneousDual F a ⊗[F] HomogeneousDual F (b + c)) :=
    (tensorTailProductSpace (S.map (homogeneousDualTensorConcat F a b).symm.toLinearMap) T).map
      ((homogeneousDualTensorConcat F b c).lTensor (HomogeneousDual F a)).toLinearMap
  change actualProductLeftCutSpace F a b c S T ≤ B
  unfold actualProductLeftCutSpace actualDualSpaceCut
  rw [Submodule.map_le_iff_le_comap]
  intro phi hphi
  obtain ⟨u, ⟨w, rfl⟩, rfl⟩ := hphi
  change (actualDualSpaceCutMap F ((a + b) + c) a (b + c) (Nat.add_assoc a b c).symm).toLinearMap
    ((homogeneousDualTensorConcat F (a + b) c).toLinearMap
      (TensorProduct.map S.subtype T.subtype w)) ∈ B
  induction w using TensorProduct.induction_on with
  | zero =>
      rw [(TensorProduct.map S.subtype T.subtype).map_zero,
        (homogeneousDualTensorConcat F (a + b) c).toLinearMap.map_zero,
        (actualDualSpaceCutMap F ((a + b) + c) a (b + c)
          (Nat.add_assoc a b c).symm).toLinearMap.map_zero]
      exact Submodule.zero_mem _
  | add x y hx hy =>
      rw [(TensorProduct.map S.subtype T.subtype).map_add,
        (homogeneousDualTensorConcat F (a + b) c).toLinearMap.map_add,
        (actualDualSpaceCutMap F ((a + b) + c) a (b + c)
          (Nat.add_assoc a b c).symm).toLinearMap.map_add]
      exact Submodule.add_mem _ hx hy
  | tmul s t =>
      rw [TensorProduct.map_tmul]
      change actualDualSpaceCutMap F ((a + b) + c) a (b + c) (Nat.add_assoc a b c).symm
        (homogeneousDualTensorConcat F (a + b) c (s.val ⊗ₜ[F] t.val)) ∈ B
      rw [actualDualSpaceCutMap_apply]
      change wordCutTensor F a (b + c)
        (homogeneousDualDegreeCast F (Nat.add_assoc a b c)
          (homogeneousDualTensorConcat F (a + b) c (s.val ⊗ₜ[F] t.val))) ∈ B
      rw [wordCutTensor_append F a b c s.val t.val]
      let s0 : S.map (homogeneousDualTensorConcat F a b).symm.toLinearMap :=
        ⟨wordCutTensor F a b s.val, ⟨s.val, s.property, rfl⟩⟩
      refine ⟨_, ⟨_, ⟨s0 ⊗ₜ[F] t, rfl⟩, rfl⟩, ?_⟩
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
      rfl

def actualProductRightCutSpace (c a b : ℕ)
    (S : Submodule F (HomogeneousDual F c)) (T : Submodule F (HomogeneousDual F (a + b))) :=
  actualDualSpaceCut F (c + (a + b)) (c + a) b (Nat.add_assoc c a b)
    (actualDualTensorProduct F c (a + b) S T)

theorem actualProductRightCutSpace_le (c a b : ℕ)
    (S : Submodule F (HomogeneousDual F c)) (T : Submodule F (HomogeneousDual F (a + b))) :
    actualProductRightCutSpace F c a b S T ≤
      (tensorFrontProductSpace S (T.map (homogeneousDualTensorConcat F a b).symm.toLinearMap)).map
        ((homogeneousDualTensorConcat F c a).rTensor (HomogeneousDual F b)).toLinearMap := by
  let B : Submodule F (HomogeneousDual F (c + a) ⊗[F] HomogeneousDual F b) :=
    (tensorFrontProductSpace S (T.map (homogeneousDualTensorConcat F a b).symm.toLinearMap)).map
      ((homogeneousDualTensorConcat F c a).rTensor (HomogeneousDual F b)).toLinearMap
  change actualProductRightCutSpace F c a b S T ≤ B
  unfold actualProductRightCutSpace actualDualSpaceCut
  rw [Submodule.map_le_iff_le_comap]
  intro phi hphi
  obtain ⟨u, ⟨w, rfl⟩, rfl⟩ := hphi
  change (actualDualSpaceCutMap F (c + (a + b)) (c + a) b (Nat.add_assoc c a b)).toLinearMap
    ((homogeneousDualTensorConcat F c (a + b)).toLinearMap
      (TensorProduct.map S.subtype T.subtype w)) ∈ B
  induction w using TensorProduct.induction_on with
  | zero =>
      rw [(TensorProduct.map S.subtype T.subtype).map_zero,
        (homogeneousDualTensorConcat F c (a + b)).toLinearMap.map_zero,
        (actualDualSpaceCutMap F (c + (a + b)) (c + a) b (Nat.add_assoc c a b)).toLinearMap.map_zero]
      exact Submodule.zero_mem _
  | add x y hx hy =>
      rw [(TensorProduct.map S.subtype T.subtype).map_add,
        (homogeneousDualTensorConcat F c (a + b)).toLinearMap.map_add,
        (actualDualSpaceCutMap F (c + (a + b)) (c + a) b (Nat.add_assoc c a b)).toLinearMap.map_add]
      exact Submodule.add_mem _ hx hy
  | tmul s t =>
      rw [TensorProduct.map_tmul]
      change actualDualSpaceCutMap F (c + (a + b)) (c + a) b (Nat.add_assoc c a b)
        (homogeneousDualTensorConcat F c (a + b) (s.val ⊗ₜ[F] t.val)) ∈ B
      rw [actualDualSpaceCutMap_apply,
        homogeneousDualDegreeCast_symm_eq F (Nat.add_assoc c a b)]
      rw [wordCutTensor_prepend F c a b s.val t.val]
      let t0 : T.map (homogeneousDualTensorConcat F a b).symm.toLinearMap :=
        ⟨wordCutTensor F a b t.val, ⟨t.val, t.property, rfl⟩⟩
      refine ⟨_, ⟨_, ⟨s ⊗ₜ[F] t0, rfl⟩, rfl⟩, ?_⟩
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
      rfl

theorem actualProductLeftCutSpace_finrank_le (a b c : ℕ)
    (S : Submodule F (HomogeneousDual F (a + b))) (T : Submodule F (HomogeneousDual F c)) :
    Module.finrank F (tensorPrefixSupport (actualProductLeftCutSpace F a b c S T)) ≤
        Module.finrank F (tensorPrefixSupport (actualDualSpaceCut F (a + b) a b rfl S)) ∧
    Module.finrank F (tensorSuffixSupport (actualProductLeftCutSpace F a b c S T)) ≤
        Module.finrank F (tensorSuffixSupport (actualDualSpaceCut F (a + b) a b rfl S)) *
          Module.finrank F T := by
  classical
  letI : FiniteDimensional F (HomogeneousDual F a) :=
    (homogeneousWordBasis F a).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (HomogeneousDual F b) :=
    (homogeneousWordBasis F b).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (HomogeneousDual F c) :=
    (homogeneousWordBasis F c).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (HomogeneousDual F (b + c)) :=
    (homogeneousWordBasis F (b + c)).dualBasis.finiteDimensional_of_finite
  have hp := tensorTailProductSpace_rightEquiv_prefixSupport_finrank_le (F := F)
    (X := HomogeneousDual F a) (Y := HomogeneousDual F b) (Z := HomogeneousDual F c)
    (A := HomogeneousDual F (b + c)) (homogeneousDualTensorConcat F b c)
      (S.map (homogeneousDualTensorConcat F a b).symm.toLinearMap) T
  have hs := tensorTailProductSpace_rightEquiv_suffixSupport_finrank_le (F := F)
    (X := HomogeneousDual F a) (Y := HomogeneousDual F b) (Z := HomogeneousDual F c)
    (A := HomogeneousDual F (b + c)) (homogeneousDualTensorConcat F b c)
      (S.map (homogeneousDualTensorConcat F a b).symm.toLinearMap) T
  rw [actualDualSpaceCut_self_add]
  exact ⟨(Submodule.finrank_mono (tensorPrefixSupport_mono (actualProductLeftCutSpace_le F a b c S T))).trans hp,
    (Submodule.finrank_mono (tensorSuffixSupport_mono (actualProductLeftCutSpace_le F a b c S T))).trans hs⟩

theorem actualProductRightCutSpace_finrank_le (c a b : ℕ)
    (S : Submodule F (HomogeneousDual F c)) (T : Submodule F (HomogeneousDual F (a + b))) :
    Module.finrank F (tensorPrefixSupport (actualProductRightCutSpace F c a b S T)) ≤
        Module.finrank F S * Module.finrank F
          (tensorPrefixSupport (actualDualSpaceCut F (a + b) a b rfl T)) ∧
    Module.finrank F (tensorSuffixSupport (actualProductRightCutSpace F c a b S T)) ≤
        Module.finrank F (tensorSuffixSupport (actualDualSpaceCut F (a + b) a b rfl T)) := by
  classical
  letI : FiniteDimensional F (HomogeneousDual F c) :=
    (homogeneousWordBasis F c).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (HomogeneousDual F a) :=
    (homogeneousWordBasis F a).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (HomogeneousDual F b) :=
    (homogeneousWordBasis F b).dualBasis.finiteDimensional_of_finite
  letI : FiniteDimensional F (HomogeneousDual F (c + a)) :=
    (homogeneousWordBasis F (c + a)).dualBasis.finiteDimensional_of_finite
  have hp := tensorFrontProductSpace_leftEquiv_prefixSupport_finrank_le (F := F)
    (X := HomogeneousDual F c) (Y := HomogeneousDual F a) (Z := HomogeneousDual F b)
    (A := HomogeneousDual F (c + a)) (homogeneousDualTensorConcat F c a) S
      (T.map (homogeneousDualTensorConcat F a b).symm.toLinearMap)
  have hs := tensorFrontProductSpace_leftEquiv_suffixSupport_finrank_le (F := F)
    (X := HomogeneousDual F c) (Y := HomogeneousDual F a) (Z := HomogeneousDual F b)
    (A := HomogeneousDual F (c + a)) (homogeneousDualTensorConcat F c a) S
      (T.map (homogeneousDualTensorConcat F a b).symm.toLinearMap)
  rw [actualDualSpaceCut_self_add]
  exact ⟨(Submodule.finrank_mono (tensorPrefixSupport_mono (actualProductRightCutSpace_le F c a b S T))).trans hp,
    (Submodule.finrank_mono (tensorSuffixSupport_mono (actualProductRightCutSpace_le F c a b S T))).trans hs⟩

/-- The four inequalities pay respectively for the two supports in each
of the two old blocks. Every literal physical cut is covered. -/
theorem actualDualTensorProduct_cutBound (m n : ℕ)
    (S : Submodule F (HomogeneousDual F m)) (T : Submodule F (HomogeneousDual F n))
    (BS BT B : ℕ) (hS : ActualDualCutBound F m S BS) (hT : ActualDualCutBound F n T BT)
    (hBS : BS ≤ B) (hBSdim : BS * Module.finrank F T ≤ B)
    (hBT : BT ≤ B) (hdimBT : Module.finrank F S * BT ≤ B) :
    ActualDualCutBound F (m + n) (actualDualTensorProduct F m n S T) B := by
  intro a b hab
  by_cases ha : a ≤ m
  · obtain ⟨c, hm⟩ := Nat.exists_eq_add_of_le ha
    have hb : b = c + n := by omega
    subst m
    subst b
    have h := actualProductLeftCutSpace_finrank_le F a c n S T
    exact ⟨h.1.trans ((hS a c rfl).1.trans hBS),
      h.2.trans ((Nat.mul_le_mul_right (Module.finrank F T) (hS a c rfl).2).trans hBSdim)⟩
  · have hma : m ≤ a := by omega
    obtain ⟨c, ha⟩ := Nat.exists_eq_add_of_le hma
    have hn : n = c + b := by omega
    subst n
    subst a
    have h := actualProductRightCutSpace_finrank_le F m c b S T
    exact ⟨h.1.trans ((Nat.mul_le_mul_left (Module.finrank F S) (hT c b rfl).1).trans hdimBT),
      h.2.trans ((hT c b rfl).2.trans hBT)⟩

#print axioms CriticalGK2.Actual.actualDualTensorProduct_cutBound

end

end CriticalGK2.Actual
