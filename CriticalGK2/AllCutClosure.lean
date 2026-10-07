import CriticalGK2.AllCutEndpoints

/-!
# Actual all-cut components are closed under multiplication by letters

Every old cut and each newly introduced endpoint is checked. The local input
is primal coherence of the dyadic annihilators.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

theorem allCutComponent_zero (W : DyadicDualData F) :
    allCutComponent F W 0 = ⊥ := by
  apply eq_bot_iff.mpr
  simpa using allCutComponent_le_rightCompletion F W 0

theorem allCutComponent_mul_letter (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) :
    productSpan F (allCutComponent F W n) (homogeneous F 1) ≤
      allCutComponent F W (n + 1) := by
  by_cases hn0 : n = 0
  · simp [hn0, allCutComponent_zero, productSpan_bot_left]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  apply le_inf
  · have h := productSpan_mono F (allCutComponent_le_homogeneous F W n)
      (le_refl (homogeneous F 1))
    simpa only [homogeneous_productSpan] using h
  · apply le_iInf
    intro j
    by_cases hj : j.val ≤ n
    · have hcut := allCutComponent_le_cut F W n j.val hj
      have hlen : (n - j.val) + 1 = n + 1 - j.val := by omega
      calc
        _ ≤ productSpan F
            (productSpan F (leftCompletion F W j.val) (homogeneous F (n - j.val)) ⊔
              productSpan F (homogeneous F j.val) (rightCompletion F W (n - j.val)))
            (homogeneous F 1) := productSpan_mono F hcut le_rfl
        _ = productSpan F (leftCompletion F W j.val)
              (homogeneous F (n + 1 - j.val)) ⊔
            productSpan F (homogeneous F j.val)
              (productSpan F (rightCompletion F W (n - j.val)) (homogeneous F 1)) := by
                rw [productSpan_sup_left, productSpan_assoc, productSpan_assoc,
                  homogeneous_productSpan, hlen]
        _ ≤ productSpan F (leftCompletion F W j.val)
              (homogeneous F (n + 1 - j.val)) ⊔
            productSpan F (homogeneous F j.val) (rightCompletion F W (n + 1 - j.val)) := by
                apply sup_le_sup le_rfl
                have h := productSpan_mono F (le_refl (homogeneous F j.val))
                  (rightCompletion_mul_letter F W hW (n - j.val))
                simpa only [hlen] using h
    · have hjlast : j.val = n + 1 := by have := j.isLt; omega
      simp only [hjlast, Nat.sub_self, rightCompletion_zero,
        productSpan_bot_right, productSpan_homogeneous_zero_right, sup_bot_eq]
      exact right_letter_new_endpoint F W hW n hn

theorem letter_mul_allCutComponent (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) :
    productSpan F (homogeneous F 1) (allCutComponent F W n) ≤
      allCutComponent F W (n + 1) := by
  by_cases hn0 : n = 0
  · simp [hn0, allCutComponent_zero, productSpan_bot_right]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  apply le_inf
  · have h := productSpan_mono F (le_refl (homogeneous F 1))
      (allCutComponent_le_homogeneous F W n)
    simpa only [homogeneous_productSpan, Nat.add_comm 1 n] using h
  · apply le_iInf
    intro j
    by_cases hj0 : j.val = 0
    · simp only [hj0, Nat.sub_zero, leftCompletion_zero, productSpan_bot_left,
        productSpan_homogeneous_zero_left, bot_sup_eq]
      exact left_letter_new_endpoint F W hW n hn
    · let i := j.val - 1
      have hi : i ≤ n := by have := j.isLt; dsimp [i]; omega
      have hij : i + 1 = j.val := by dsimp [i]; omega
      have hji : 1 + i = j.val := by omega
      have hlen : n - i = n + 1 - j.val := by omega
      have hcut := allCutComponent_le_cut F W n i hi
      calc
        _ ≤ productSpan F (homogeneous F 1)
            (productSpan F (leftCompletion F W i) (homogeneous F (n - i)) ⊔
              productSpan F (homogeneous F i) (rightCompletion F W (n - i))) :=
                productSpan_mono F le_rfl hcut
        _ = productSpan F
              (productSpan F (homogeneous F 1) (leftCompletion F W i))
              (homogeneous F (n + 1 - j.val)) ⊔
            productSpan F (homogeneous F j.val)
              (rightCompletion F W (n + 1 - j.val)) := by
                rw [productSpan_sup_right, ← productSpan_assoc, ← productSpan_assoc,
                  homogeneous_productSpan, hji, hlen]
        _ ≤ productSpan F (leftCompletion F W j.val)
              (homogeneous F (n + 1 - j.val)) ⊔
            productSpan F (homogeneous F j.val)
              (rightCompletion F W (n + 1 - j.val)) := by
                apply sup_le_sup _ le_rfl
                have h := productSpan_mono F (letter_mul_leftCompletion F W hW i)
                  (le_refl (homogeneous F (n + 1 - j.val)))
                simpa only [hij] using h

end

end CriticalGK2.Actual
