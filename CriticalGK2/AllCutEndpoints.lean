import CriticalGK2.CompletionSteps

/-!
# The new endpoint cuts under multiplication by an actual letter

The endpoint-cut identities follow from the internal cut
`i = n + 1 - 2^m` and both terms of primal coherence.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

theorem allCutComponent_le_cut (W : DyadicDualData F) (n i : ℕ) (hi : i ≤ n) :
    allCutComponent F W n ≤
      productSpan F (leftCompletion F W i) (homogeneous F (n - i)) ⊔
      productSpan F (homogeneous F i) (rightCompletion F W (n - i)) := by
  exact inf_le_right.trans (iInf_le _ (⟨i, by omega⟩ : Fin (n + 1)))

theorem productSpan_sandwich_sup (S A B C D T : Submodule F (WordAlgebra F)) :
    productSpan F S
      (productSpan F (productSpan F A B ⊔ productSpan F C D) T) =
      productSpan F (productSpan F S A) (productSpan F B T) ⊔
      productSpan F (productSpan F S C) (productSpan F D T) := by
  rw [productSpan_sup_left, productSpan_sup_right,
    productSpan_sandwich_assoc, productSpan_sandwich_assoc]

theorem right_letter_new_endpoint (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : 0 < n) :
    productSpan F (allCutComponent F W n) (homogeneous F 1) ≤
      leftCompletion F W (n + 1) := by
  obtain ⟨m, i, δ, hm, hi, hni, hδ, hδroot, hroot⟩ := exists_endpoint_cut n hn
  have hq2 : 2 ≤ (2 : ℕ) ^ m := by
    have h : (2 : ℕ) ^ 1 ≤ 2 ^ m := by gcongr <;> omega
    simpa using h
  have hqi : i ≤ n := by omega
  have hgap : n - i = 2 ^ m - 1 := by omega
  have hδi : δ + i = 2 ^ m := by omega
  have hqminus : (2 ^ m - 1) + 1 = 2 ^ m := by omega
  have hL : productSpan F (homogeneous F δ) (leftCompletion F W i) ≤
      ambientAnnihilator F W m := by
    by_cases hi0 : i = 0
    · simp [hi0, productSpan_bot_right]
    · rw [hδ]
      exact leftCompletion_extension F W hW i (Nat.pos_of_ne_zero hi0) m
        (strictDyadicRoot_le_of_lt_pow (Nat.pos_of_ne_zero hi0) hi)
  have hR : productSpan F (rightCompletion F W (2 ^ m - 1)) (homogeneous F 1) ≤
      ambientAnnihilator F W m := by
    have hnq : 0 < (2 : ℕ) ^ m - 1 := by omega
    have hlt : (2 : ℕ) ^ m - 1 < 2 ^ m := by omega
    have h := rightCompletion_extension F W hW (2 ^ m - 1) hnq m
      (strictDyadicRoot_le_of_lt_pow hnq hlt)
    have heq : (2 : ℕ) ^ m - (2 ^ m - 1) = 1 := by omega
    simpa only [heq] using h
  have hcut := allCutComponent_le_cut F W n i hqi
  rw [hgap] at hcut
  have hprod : productSpan F (homogeneous F δ)
      (productSpan F (allCutComponent F W n) (homogeneous F 1)) ≤
        ambientAnnihilator F W (m + 1) := by
    calc
      _ ≤ productSpan F (homogeneous F δ)
          (productSpan F
            (productSpan F (leftCompletion F W i) (homogeneous F (2 ^ m - 1)) ⊔
              productSpan F (homogeneous F i) (rightCompletion F W (2 ^ m - 1)))
            (homogeneous F 1)) :=
          productSpan_mono F le_rfl (productSpan_mono F hcut le_rfl)
      _ = productSpan F (productSpan F (homogeneous F δ) (leftCompletion F W i))
            (homogeneous F (2 ^ m)) ⊔
          productSpan F (homogeneous F (2 ^ m))
            (productSpan F (rightCompletion F W (2 ^ m - 1)) (homogeneous F 1)) := by
              rw [productSpan_sandwich_sup, homogeneous_productSpan,
                homogeneous_productSpan, hqminus, hδi]
      _ ≤ productSpan F (ambientAnnihilator F W m) (homogeneous F (2 ^ m)) ⊔
          productSpan F (homogeneous F (2 ^ m)) (ambientAnnihilator F W m) :=
            sup_le_sup (productSpan_mono F hL le_rfl) (productSpan_mono F le_rfl hR)
      _ ≤ ambientAnnihilator F W (m + 1) := hW m
  apply le_leftCompletion_of_product F W (n + 1) (by omega)
  · have h := productSpan_mono F (allCutComponent_le_homogeneous F W n)
      (le_refl (homogeneous F 1))
    simpa only [homogeneous_productSpan] using h
  · rw [← hδroot, hroot]
    exact hprod

theorem left_letter_new_endpoint (W : DyadicDualData F)
    (hW : PrimalCoherent F W) (n : ℕ) (hn : 0 < n) :
    productSpan F (homogeneous F 1) (allCutComponent F W n) ≤
      rightCompletion F W (n + 1) := by
  obtain ⟨m, i, δ, hm, hi, hni, hδ, hδroot, hroot⟩ := exists_endpoint_cut n hn
  have hq2 : 2 ≤ (2 : ℕ) ^ m := by
    have h : (2 : ℕ) ^ 1 ≤ 2 ^ m := by gcongr <;> omega
    simpa using h
  have hqi : 2 ^ m - 1 ≤ n := by omega
  have hgap : n - (2 ^ m - 1) = i := by omega
  have hiδ : i + δ = 2 ^ m := by omega
  have hqminus : 1 + (2 ^ m - 1) = 2 ^ m := by omega
  have hR : productSpan F (rightCompletion F W i) (homogeneous F δ) ≤
      ambientAnnihilator F W m := by
    by_cases hi0 : i = 0
    · simp [hi0, productSpan_bot_left]
    · rw [hδ]
      exact rightCompletion_extension F W hW i (Nat.pos_of_ne_zero hi0) m
        (strictDyadicRoot_le_of_lt_pow (Nat.pos_of_ne_zero hi0) hi)
  have hL : productSpan F (homogeneous F 1) (leftCompletion F W (2 ^ m - 1)) ≤
      ambientAnnihilator F W m := by
    have hnq : 0 < (2 : ℕ) ^ m - 1 := by omega
    have hlt : (2 : ℕ) ^ m - 1 < 2 ^ m := by omega
    have h := leftCompletion_extension F W hW (2 ^ m - 1) hnq m
      (strictDyadicRoot_le_of_lt_pow hnq hlt)
    have heq : (2 : ℕ) ^ m - (2 ^ m - 1) = 1 := by omega
    simpa only [heq] using h
  have hcut := allCutComponent_le_cut F W n (2 ^ m - 1) hqi
  rw [hgap] at hcut
  have hprod : productSpan F
      (productSpan F (homogeneous F 1) (allCutComponent F W n)) (homogeneous F δ) ≤
        ambientAnnihilator F W (m + 1) := by
    calc
      _ = productSpan F (homogeneous F 1)
          (productSpan F (allCutComponent F W n) (homogeneous F δ)) :=
            productSpan_assoc F _ _ _
      _ ≤ productSpan F (homogeneous F 1)
          (productSpan F
            (productSpan F (leftCompletion F W (2 ^ m - 1)) (homogeneous F i) ⊔
              productSpan F (homogeneous F (2 ^ m - 1)) (rightCompletion F W i))
            (homogeneous F δ)) :=
          productSpan_mono F le_rfl (productSpan_mono F hcut le_rfl)
      _ = productSpan F
            (productSpan F (homogeneous F 1) (leftCompletion F W (2 ^ m - 1)))
            (homogeneous F (2 ^ m)) ⊔
          productSpan F (homogeneous F (2 ^ m))
            (productSpan F (rightCompletion F W i) (homogeneous F δ)) := by
              rw [productSpan_sandwich_sup, homogeneous_productSpan,
                homogeneous_productSpan, hiδ, hqminus]
      _ ≤ productSpan F (ambientAnnihilator F W m) (homogeneous F (2 ^ m)) ⊔
          productSpan F (homogeneous F (2 ^ m)) (ambientAnnihilator F W m) :=
            sup_le_sup (productSpan_mono F hL le_rfl) (productSpan_mono F le_rfl hR)
      _ ≤ ambientAnnihilator F W (m + 1) := hW m
  apply le_rightCompletion_of_product F W (n + 1) (by omega)
  · have h := productSpan_mono F (le_refl (homogeneous F 1))
      (allCutComponent_le_homogeneous F W n)
    simpa only [homogeneous_productSpan, Nat.add_comm 1 n] using h
  · rw [← hδroot, hroot]
    exact hprod

end

end CriticalGK2.Actual
