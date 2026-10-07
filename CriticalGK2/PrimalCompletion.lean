import Mathlib
import CriticalGK2.DyadicRoots

/-!
# Actual completion spaces at every larger dyadic root

The parameter is the literal family of dyadic dual subspaces from
`ActualWordSpaces`. Under primal coherence, the theorems identify completion
spaces at larger dyadic roots. The sparse-dual construction establishes this
coherence for its family.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- The literal annihilator coherence appearing in equation U-coherence. -/
def PrimalCoherent (W : DyadicDualData F) : Prop :=
  ∀ h : ℕ,
    productSpan F (ambientAnnihilator F W h) (homogeneous F (2 ^ h)) ⊔
      productSpan F (homogeneous F (2 ^ h)) (ambientAnnihilator F W h) ≤
        ambientAnnihilator F W (h + 1)

theorem rightCompletion_le_homogeneous (W : DyadicDualData F) (n : ℕ) :
    rightCompletion F W n ≤ homogeneous F n := by
  by_cases hn : n = 0
  · simp [rightCompletion, hn]
  · simp only [rightCompletion, if_neg hn]
    exact inf_le_left

theorem leftCompletion_le_homogeneous (W : DyadicDualData F) (n : ℕ) :
    leftCompletion F W n ≤ homogeneous F n := by
  by_cases hn : n = 0
  · simp [leftCompletion, hn]
  · simp only [leftCompletion, if_neg hn]
    exact inf_le_left

theorem rightCompletion_root_product (W : DyadicDualData F) (n : ℕ) (hn : 0 < n) :
    productSpan F (rightCompletion F W n)
      (homogeneous F (2 ^ strictDyadicRoot n - n)) ≤
        ambientAnnihilator F W (strictDyadicRoot n) := by
  rw [productSpan_le_iff]
  intro x hx y hy
  have hx' : x ∈ homogeneous F n ∧
      ∀ b : homogeneous F (2 ^ strictDyadicRoot n - n),
        x * b.val ∈ ambientAnnihilator F W (strictDyadicRoot n) := by
    simpa only [rightCompletion, if_neg (Nat.ne_of_gt hn), Submodule.mem_inf,
      Submodule.mem_iInf, Submodule.mem_comap, rightMultiplication] using hx
  exact hx'.2 ⟨y, hy⟩

theorem leftCompletion_root_product (W : DyadicDualData F) (n : ℕ) (hn : 0 < n) :
    productSpan F (homogeneous F (2 ^ strictDyadicRoot n - n))
      (leftCompletion F W n) ≤
        ambientAnnihilator F W (strictDyadicRoot n) := by
  rw [productSpan_le_iff]
  intro x hx y hy
  have hy' : y ∈ homogeneous F n ∧
      ∀ a : homogeneous F (2 ^ strictDyadicRoot n - n),
        a.val * y ∈ ambientAnnihilator F W (strictDyadicRoot n) := by
    simpa only [leftCompletion, if_neg (Nat.ne_of_gt hn), Submodule.mem_inf,
      Submodule.mem_iInf, Submodule.mem_comap, leftMultiplication] using hy
  exact hy'.2 ⟨x, hx⟩

theorem rightCompletion_extension (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : 0 < n)
    (J : ℕ) (hJ : strictDyadicRoot n ≤ J) :
    productSpan F (rightCompletion F W n) (homogeneous F (2 ^ J - n)) ≤
      ambientAnnihilator F W J := by
  induction J, hJ using Nat.le_induction with
  | base => exact rightCompletion_root_product F W n hn
  | succ J hJ ih =>
      have hpow : 2 ^ strictDyadicRoot n ≤ (2 : ℕ) ^ J := by gcongr <;> norm_num
      have hnJ : n ≤ 2 ^ J :=
        Nat.le_of_lt ((lt_strictDyadicRoot_pow n).trans_le hpow)
      have hgap : (2 ^ J - n) + 2 ^ J = 2 ^ (J + 1) - n := by
        rw [pow_succ]
        omega
      calc
        productSpan F (rightCompletion F W n) (homogeneous F (2 ^ (J + 1) - n))
          = productSpan F (rightCompletion F W n)
              (productSpan F (homogeneous F (2 ^ J - n)) (homogeneous F (2 ^ J))) := by
                  rw [homogeneous_productSpan, hgap]
        _ = productSpan F
              (productSpan F (rightCompletion F W n) (homogeneous F (2 ^ J - n)))
              (homogeneous F (2 ^ J)) := (productSpan_assoc F _ _ _).symm
        _ ≤ productSpan F (ambientAnnihilator F W J) (homogeneous F (2 ^ J)) :=
              productSpan_mono F ih le_rfl
        _ ≤ ambientAnnihilator F W (J + 1) := (le_sup_left.trans (hW J))

theorem leftCompletion_extension (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : 0 < n)
    (J : ℕ) (hJ : strictDyadicRoot n ≤ J) :
    productSpan F (homogeneous F (2 ^ J - n)) (leftCompletion F W n) ≤
      ambientAnnihilator F W J := by
  induction J, hJ using Nat.le_induction with
  | base => exact leftCompletion_root_product F W n hn
  | succ J hJ ih =>
      have hpow : 2 ^ strictDyadicRoot n ≤ (2 : ℕ) ^ J := by gcongr <;> norm_num
      have hnJ : n ≤ 2 ^ J :=
        Nat.le_of_lt ((lt_strictDyadicRoot_pow n).trans_le hpow)
      have hgap : 2 ^ J + (2 ^ J - n) = 2 ^ (J + 1) - n := by
        rw [pow_succ]
        omega
      calc
        productSpan F (homogeneous F (2 ^ (J + 1) - n)) (leftCompletion F W n)
          = productSpan F
              (productSpan F (homogeneous F (2 ^ J)) (homogeneous F (2 ^ J - n)))
              (leftCompletion F W n) := by rw [homogeneous_productSpan, hgap]
        _ = productSpan F (homogeneous F (2 ^ J))
              (productSpan F (homogeneous F (2 ^ J - n)) (leftCompletion F W n)) :=
                productSpan_assoc F _ _ _
        _ ≤ productSpan F (homogeneous F (2 ^ J)) (ambientAnnihilator F W J) :=
              productSpan_mono F le_rfl ih
        _ ≤ ambientAnnihilator F W (J + 1) := (le_sup_right.trans (hW J))

end

end CriticalGK2.Actual
