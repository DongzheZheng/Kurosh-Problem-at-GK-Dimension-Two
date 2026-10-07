import CriticalGK2.ActualWordSpaces

/-!
# Linear product interfaces in the actual two-letter word algebra

All spaces and products in this file are the actual subspaces of
`MonoidAlgebra F (FreeMonoid Bool)` from `ActualWordSpaces`.  These interfaces
are used by the dyadic completion and all-cut ideal-closure proofs.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

theorem productSpan_mono_le
    {S S' T T' : Submodule F (WordAlgebra F)} (hS : S ≤ S') (hT : T ≤ T') :
    productSpan F S T ≤ productSpan F S' T' := productSpan_mono F hS hT

theorem productSpan_le_of_le_left
    {S S' T : Submodule F (WordAlgebra F)} (hS : S ≤ S') :
    productSpan F S T ≤ productSpan F S' T := productSpan_mono F hS le_rfl

theorem productSpan_le_of_le_right
    {S T T' : Submodule F (WordAlgebra F)} (hT : T ≤ T') :
    productSpan F S T ≤ productSpan F S T' := productSpan_mono F le_rfl hT

/-- Actual linear spans distribute over a sum of spaces in the first factor. -/
theorem productSpan_sup_left (S T U : Submodule F (WordAlgebra F)) :
    productSpan F (S ⊔ T) U = productSpan F S U ⊔ productSpan F T U := by
  apply le_antisymm
  · rw [productSpan_le_iff]
    intro x hx y hy
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    rw [add_mul]
    exact (productSpan F S U ⊔ productSpan F T U).add_mem
      ((show productSpan F S U ≤ productSpan F S U ⊔ productSpan F T U from le_sup_left)
        (mul_mem_productSpan F hs hy))
      ((show productSpan F T U ≤ productSpan F S U ⊔ productSpan F T U from le_sup_right)
        (mul_mem_productSpan F ht hy))
  · exact sup_le (productSpan_mono F le_sup_left le_rfl)
      (productSpan_mono F le_sup_right le_rfl)

/-- Actual linear spans distribute over a sum of spaces in the second factor. -/
theorem productSpan_sup_right (S T U : Submodule F (WordAlgebra F)) :
    productSpan F S (T ⊔ U) = productSpan F S T ⊔ productSpan F S U := by
  apply le_antisymm
  · rw [productSpan_le_iff]
    intro x hx y hy
    obtain ⟨t, ht, u, hu, rfl⟩ := Submodule.mem_sup.mp hy
    rw [mul_add]
    exact (productSpan F S T ⊔ productSpan F S U).add_mem
      ((show productSpan F S T ≤ productSpan F S T ⊔ productSpan F S U from le_sup_left)
        (mul_mem_productSpan F hx ht))
      ((show productSpan F S U ≤ productSpan F S T ⊔ productSpan F S U from le_sup_right)
        (mul_mem_productSpan F hx hu))
  · exact sup_le (productSpan_mono F le_rfl le_sup_left)
      (productSpan_mono F le_rfl le_sup_right)

/-- Sandwiching by an actual homogeneous space on the left and the right
can be reassociated using actual algebra multiplication. -/
theorem productSpan_sandwich_assoc (S T U P : Submodule F (WordAlgebra F)) :
    productSpan F S (productSpan F (productSpan F T U) P) =
      productSpan F (productSpan F S T) (productSpan F U P) := by
  rw [productSpan_assoc, ← productSpan_assoc]

end

end CriticalGK2.Actual
