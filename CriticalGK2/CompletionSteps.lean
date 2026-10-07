import CriticalGK2.PrimalCompletion
import CriticalGK2.WordProducts

/-!
# Literal completion spaces: membership and multiplication by a letter

All spaces here are the actual submodules of the actual free word algebra.
The explicit input `PrimalCoherent` remains a local coherence statement.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

theorem le_rightCompletion_of_product (W : DyadicDualData F) (n : ℕ)
    (hn : 0 < n) (S : Submodule F (WordAlgebra F))
    (hS : S ≤ homogeneous F n)
    (hprod : productSpan F S (homogeneous F (2 ^ strictDyadicRoot n - n)) ≤
      ambientAnnihilator F W (strictDyadicRoot n)) :
    S ≤ rightCompletion F W n := by
  intro x hx
  simp only [rightCompletion, if_neg (Nat.ne_of_gt hn), Submodule.mem_inf,
    Submodule.mem_iInf, Submodule.mem_comap]
  refine ⟨hS hx, ?_⟩
  intro b
  exact hprod (mul_mem_productSpan F hx b.property)

theorem le_leftCompletion_of_product (W : DyadicDualData F) (n : ℕ)
    (hn : 0 < n) (S : Submodule F (WordAlgebra F))
    (hS : S ≤ homogeneous F n)
    (hprod : productSpan F (homogeneous F (2 ^ strictDyadicRoot n - n)) S ≤
      ambientAnnihilator F W (strictDyadicRoot n)) :
    S ≤ leftCompletion F W n := by
  intro x hx
  simp only [leftCompletion, if_neg (Nat.ne_of_gt hn), Submodule.mem_inf,
    Submodule.mem_iInf, Submodule.mem_comap]
  refine ⟨hS hx, ?_⟩
  intro a
  exact hprod (mul_mem_productSpan F a.property hx)

theorem rightCompletion_mul_letter (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) :
    productSpan F (rightCompletion F W n) (homogeneous F 1) ≤
      rightCompletion F W (n + 1) := by
  by_cases hn : n = 0
  · simp [hn, productSpan_bot_left]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let J := strictDyadicRoot (n + 1)
  have hJ : strictDyadicRoot n ≤ J :=
    strictDyadicRoot_monotone (Nat.le_succ n)
  have hbound : n + 1 < 2 ^ J := lt_strictDyadicRoot_pow (n + 1)
  have hgap : 1 + (2 ^ J - (n + 1)) = 2 ^ J - n := by omega
  apply le_rightCompletion_of_product F W (n + 1) (by omega)
  · have h := productSpan_mono F (rightCompletion_le_homogeneous F W n)
      (le_refl (homogeneous F 1))
    simpa only [homogeneous_productSpan] using h
  · change productSpan F
        (productSpan F (rightCompletion F W n) (homogeneous F 1))
        (homogeneous F (2 ^ J - (n + 1))) ≤ ambientAnnihilator F W J
    rw [productSpan_assoc, homogeneous_productSpan, hgap]
    exact rightCompletion_extension F W hW n hnpos J hJ

theorem letter_mul_leftCompletion (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) :
    productSpan F (homogeneous F 1) (leftCompletion F W n) ≤
      leftCompletion F W (n + 1) := by
  by_cases hn : n = 0
  · simp [hn, productSpan_bot_right]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let J := strictDyadicRoot (n + 1)
  have hJ : strictDyadicRoot n ≤ J :=
    strictDyadicRoot_monotone (Nat.le_succ n)
  have hbound : n + 1 < 2 ^ J := lt_strictDyadicRoot_pow (n + 1)
  have hgap : (2 ^ J - (n + 1)) + 1 = 2 ^ J - n := by omega
  apply le_leftCompletion_of_product F W (n + 1) (by omega)
  · have h := productSpan_mono F (le_refl (homogeneous F 1))
      (leftCompletion_le_homogeneous F W n)
    simpa only [homogeneous_productSpan, Nat.add_comm 1 n] using h
  · change productSpan F (homogeneous F (2 ^ J - (n + 1)))
        (productSpan F (homogeneous F 1) (leftCompletion F W n)) ≤
      ambientAnnihilator F W J
    rw [← productSpan_assoc, homogeneous_productSpan, hgap]
    exact leftCompletion_extension F W hW n hnpos J hJ

end

end CriticalGK2.Actual
