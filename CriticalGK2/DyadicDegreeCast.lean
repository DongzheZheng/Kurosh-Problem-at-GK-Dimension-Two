import CriticalGK2.ActualWordSpaces

/-!
# Explicit degree transport at actual dyadic cuts

The types of the actual homogeneous spaces contain their lengths.  The two
old blocks have length `2^h + 2^h`, while the new dyadic block has length
`2^(h+1)`.  This file records the literal equality and the induced primal and
dual equivalences, including their proved evaluation compatibility.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

theorem dyadicDoubleDegree (h : ℕ) : 2 ^ h + 2 ^ h = 2 ^ (h + 1) := by
  rw [pow_succ]
  omega

def homogeneousDegreeCast {a b : ℕ} (hab : a = b) :
    homogeneous F a ≃ₗ[F] homogeneous F b := by
  subst b
  exact LinearEquiv.refl F (homogeneous F a)

def homogeneousDualDegreeCast {a b : ℕ} (hab : a = b) :
    HomogeneousDual F a ≃ₗ[F] HomogeneousDual F b := by
  subst b
  exact LinearEquiv.refl F (HomogeneousDual F a)

@[simp]
theorem homogeneousDegreeCast_coe {a b : ℕ} (hab : a = b)
    (x : homogeneous F a) : (homogeneousDegreeCast F hab x).val = x.val := by
  subst b
  rfl

@[simp]
theorem homogeneousDualDegreeCast_pairing {a b : ℕ} (hab : a = b)
    (φ : HomogeneousDual F a) (x : homogeneous F a) :
    homogeneousDualDegreeCast F hab φ (homogeneousDegreeCast F hab x) = φ x := by
  subst b
  rfl

theorem homogeneousDualDegreeCast_symm_pairing {a b : ℕ} (hab : a = b)
    (φ : HomogeneousDual F b) (x : homogeneous F a) :
    φ (homogeneousDegreeCast F hab x) = (homogeneousDualDegreeCast F hab).symm φ x := by
  subst b
  rfl

/-- Membership in an actual annihilator transports through the proved
primal and dual degree equivalences. -/
theorem homogeneousDegreeCast_mem_annihilator_iff {a b : ℕ} (hab : a = b)
    (W : Submodule F (HomogeneousDual F b)) (x : homogeneous F a) :
    homogeneousDegreeCast F hab x ∈ W.dualCoannihilator ↔
      x ∈ (W.comap (homogeneousDualDegreeCast F hab).toLinearMap).dualCoannihilator := by
  subst b
  simp [homogeneousDegreeCast, homogeneousDualDegreeCast]

end

end CriticalGK2.Actual
