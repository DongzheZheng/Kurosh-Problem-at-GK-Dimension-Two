import CriticalGK2.ActualWordSpaces

/-!
# Actual all-cut homogeneous components survive

The only hypothesis is nonzeroness of the actual dual space at the root read
by a given degree. This gives nontriviality of the corresponding
homogeneous quotient component.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

theorem degree_lt_strictDyadicPower (n : ℕ) : n < 2 ^ strictDyadicRoot n :=
  Nat.lt_pow_succ_log_self (by decide) n

theorem homogeneous_mem_ambientAnnihilator_iff
    (W : DyadicDualData F) (h : ℕ) (x : homogeneous F (2 ^ h)) :
    x.val ∈ ambientAnnihilator F W h ↔ x ∈ dyadicAnnihilator F W h := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx
    have hyx : y = x := Subtype.ext hxy
    simpa only [hyx] using hy
  · intro hx
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

theorem dyadicAnnihilator_ne_top_of_dual_ne_bot
    (W : DyadicDualData F) (h : ℕ) (hW : W h ≠ ⊥) :
    dyadicAnnihilator F W h ≠ ⊤ := by
  intro hU
  apply hW
  apply eq_bot_iff.mpr
  intro φ hφ
  change φ = 0
  apply LinearMap.ext
  intro x
  have hx : x ∈ dyadicAnnihilator F W h := by
    rw [hU]
    exact Submodule.mem_top
  exact (mem_dyadicAnnihilator_iff F W h x).mp hx φ hφ

theorem homogeneous_not_le_ambientAnnihilator
    (W : DyadicDualData F) (h : ℕ) (hW : W h ≠ ⊥) :
    ¬ homogeneous F (2 ^ h) ≤ ambientAnnihilator F W h := by
  intro hle
  apply dyadicAnnihilator_ne_top_of_dual_ne_bot F W h hW
  apply eq_top_iff.mpr
  intro x hx
  exact (homogeneous_mem_ambientAnnihilator_iff F W h x).mp (hle x.property)

/-- The actual right completion is a proper subspace of degree n.  This uses
the proved equality H_n H_(q-n)=H_q and the actual dual annihilator. -/
theorem homogeneous_not_le_rightCompletion
    (W : DyadicDualData F) (n : ℕ) (hn : n ≠ 0)
    (hW : W (strictDyadicRoot n) ≠ ⊥) :
    ¬ homogeneous F n ≤ rightCompletion F W n := by
  intro hle
  have hprod :
      productSpan F (homogeneous F n) (homogeneous F (2 ^ strictDyadicRoot n - n)) ≤
        ambientAnnihilator F W (strictDyadicRoot n) := by
    rw [productSpan_le_iff]
    intro x hx y hy
    have hx' := hle hx
    rw [rightCompletion, if_neg hn] at hx'
    have hxy := (Submodule.mem_iInf _).mp hx'.2
      (⟨y, hy⟩ : homogeneous F (2 ^ strictDyadicRoot n - n))
    exact hxy
  have hq : n + (2 ^ strictDyadicRoot n - n) = 2 ^ strictDyadicRoot n :=
    Nat.add_sub_of_le (degree_lt_strictDyadicPower n).le
  rw [homogeneous_productSpan, hq] at hprod
  exact homogeneous_not_le_ambientAnnihilator F W (strictDyadicRoot n) hW hprod

theorem allCutComponent_ne_homogeneous
    (W : DyadicDualData F) (n : ℕ) (hn : n ≠ 0)
    (hW : W (strictDyadicRoot n) ≠ ⊥) :
    allCutComponent F W n ≠ homogeneous F n := by
  intro heq
  apply homogeneous_not_le_rightCompletion F W n hn hW
  rw [← heq]
  exact allCutComponent_le_rightCompletion F W n

/-- The homogeneous quotient component is nontrivial. -/
theorem componentQuotient_nontrivial
    (W : DyadicDualData F) (n : ℕ) (hn : n ≠ 0)
    (hW : W (strictDyadicRoot n) ≠ ⊥) :
    Nontrivial (ComponentQuotient F W n) := by
  apply Submodule.Quotient.nontrivial_iff.mpr
  intro htop
  apply allCutComponent_ne_homogeneous F W n hn hW
  apply le_antisymm (allCutComponent_le_homogeneous F W n)
  intro x hx
  have hx' : (⟨x, hx⟩ : homogeneous F n) ∈
      (allCutComponent F W n).comap (homogeneous F n).subtype := by
    rw [htop]
    exact Submodule.mem_top
  exact hx'

end

end CriticalGK2.Actual
