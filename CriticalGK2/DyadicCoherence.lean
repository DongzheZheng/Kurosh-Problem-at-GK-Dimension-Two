import CriticalGK2.PrimalCompletion
import CriticalGK2.WordCoherence
import CriticalGK2.DyadicDegreeCast

/-!
# Raw dyadic dual inclusion implies actual primal coherence

The explicit input is the raw inclusion W_(h+1) ⊆ W_h ⊗ W_h in the
manuscript, interpreted through the proved actual word tensor and degree
equivalences. This inclusion implies primal coherence.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- Raw dyadic inclusion expressed after putting both sides in the same
actual length-indexed dual space. -/
def DualCoherent (W : DyadicDualData F) : Prop :=
  ∀ h : ℕ,
    (W (h + 1)).comap
      (homogeneousDualDegreeCast F (dyadicDoubleDegree h)).toLinearMap ≤
        actualDualTensorProduct F (2 ^ h) (2 ^ h) (W h) (W h)

/-- The common-degree formulation is precisely the original tensor-block
inclusion, transported forward by the actual degree equivalence. -/
theorem dualCoherent_iff_forward_inclusion (W : DyadicDualData F) :
    DualCoherent F W ↔
      ∀ h : ℕ, W (h + 1) ≤
        (actualDualTensorProduct F (2 ^ h) (2 ^ h) (W h) (W h)).map
          (homogeneousDualDegreeCast F (dyadicDoubleDegree h)).toLinearMap := by
  constructor
  · intro hW h φ hφ
    let φ' := (homogeneousDualDegreeCast F (dyadicDoubleDegree h)).symm φ
    have hφ' : φ' ∈ (W (h + 1)).comap
        (homogeneousDualDegreeCast F (dyadicDoubleDegree h)).toLinearMap := by
      change homogeneousDualDegreeCast F (dyadicDoubleDegree h) φ' ∈ W (h + 1)
      simpa only [φ', LinearEquiv.apply_symm_apply] using hφ
    exact Submodule.mem_map.mpr ⟨φ', hW h hφ', by simp [φ']⟩
  · intro hW h φ hφ
    have hmem := hW h hφ
    obtain ⟨ψ, hψ, hψφ⟩ := Submodule.mem_map.mp hmem
    have heq : ψ = φ :=
      (homogeneousDualDegreeCast F (dyadicDoubleDegree h)).injective hψφ
    simpa only [heq] using hψ

/-- Derive both actual U-coherence inclusions from the raw W-coherence. -/
theorem dualCoherent_primalCoherent (W : DyadicDualData F)
    (hW : DualCoherent F W) : PrimalCoherent F W := by
  intro h
  apply sup_le
  · rw [productSpan_le_iff]
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
    let y' : homogeneous F (2 ^ h) := ⟨y, hy⟩
    let next := (W (h + 1)).comap
      (homogeneousDualDegreeCast F (dyadicDoubleDegree h)).toLinearMap
    have hprod : homogeneousMultiplication F (2 ^ h) (2 ^ h) x' y' ∈
        next.dualCoannihilator :=
      homogeneousMultiplication_mem_dualCoannihilator_left F (2 ^ h) (2 ^ h)
        (W h) (W h) next (hW h) x' y' hx'
    have hz : homogeneousDegreeCast F (dyadicDoubleDegree h)
        (homogeneousMultiplication F (2 ^ h) (2 ^ h) x' y') ∈
        dyadicAnnihilator F W (h + 1) :=
      (homogeneousDegreeCast_mem_annihilator_iff F (dyadicDoubleDegree h)
        (W (h + 1)) _).mpr hprod
    refine Submodule.mem_map.mpr ⟨_, hz, ?_⟩
    change (homogeneousDegreeCast F (dyadicDoubleDegree h)
      (homogeneousMultiplication F (2 ^ h) (2 ^ h) x' y')).val = x'.val * y
    rw [homogeneousDegreeCast_coe]
    rfl
  · rw [productSpan_le_iff]
    intro x hx y hy
    obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.mp hy
    let x' : homogeneous F (2 ^ h) := ⟨x, hx⟩
    let next := (W (h + 1)).comap
      (homogeneousDualDegreeCast F (dyadicDoubleDegree h)).toLinearMap
    have hprod : homogeneousMultiplication F (2 ^ h) (2 ^ h) x' y' ∈
        next.dualCoannihilator :=
      homogeneousMultiplication_mem_dualCoannihilator_right F (2 ^ h) (2 ^ h)
        (W h) (W h) next (hW h) x' y' hy'
    have hz : homogeneousDegreeCast F (dyadicDoubleDegree h)
        (homogeneousMultiplication F (2 ^ h) (2 ^ h) x' y') ∈
        dyadicAnnihilator F W (h + 1) :=
      (homogeneousDegreeCast_mem_annihilator_iff F (dyadicDoubleDegree h)
        (W (h + 1)) _).mpr hprod
    refine Submodule.mem_map.mpr ⟨_, hz, ?_⟩
    change (homogeneousDegreeCast F (dyadicDoubleDegree h)
      (homogeneousMultiplication F (2 ^ h) (2 ^ h) x' y')).val = x * y'.val
    rw [homogeneousDegreeCast_coe]
    rfl

end

end CriticalGK2.Actual
