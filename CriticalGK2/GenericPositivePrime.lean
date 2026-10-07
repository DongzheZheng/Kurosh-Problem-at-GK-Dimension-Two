import CriticalGK2.HomogeneousPrimeQuotient

/-!
# Ordinary primeness of a genuine positive subalgebra

For each ordinary non-unital ring ideal of S, take the F-linear span of
its image in B. The decomposition B = F*1 + S makes this span a B-ideal.
Scalar bilinearity preserves zero products of the original ideals, so the
argument applies to all ordinary ideals of S.

The hypotheses are primeness of B, the scalar-plus-positive decomposition,
and a nonzero element of S.
-/

namespace CriticalGK2.PrimeInheritance

noncomputable section

variable (F : Type*) [Field F]
variable {B : Type*} [Ring B] [Algebra F B]

def leftProduct (b : B) : B →ₗ[F] B where
  toFun x := b * x
  map_add' x y := mul_add b x y
  map_smul' c x := by simp only [mul_smul_comm, RingHom.id_apply]

def rightProduct (b : B) : B →ₗ[F] B where
  toFun x := x * b
  map_add' x y := add_mul x y b
  map_smul' c x := by simp only [smul_mul_assoc, RingHom.id_apply]

def ordinaryIdealLinearSpan (S : NonUnitalSubalgebra F B) (J : TwoSidedIdeal S) :
    Submodule F B := Submodule.span F (Subtype.val '' (J : Set S))

theorem ordinaryIdealLinearSpan_mem (S : NonUnitalSubalgebra F B)
    (J : TwoSidedIdeal S) (u : S) (hu : u ∈ J) : u.val ∈ ordinaryIdealLinearSpan F S J :=
  Submodule.subset_span ⟨u, hu, rfl⟩

theorem ordinaryIdealLinearSpan_mul_left (S : NonUnitalSubalgebra F B)
    (hsplit : ∀ b : B, ∃ c : F, ∃ s : S, b = c • (1 : B) + s.val)
    (J : TwoSidedIdeal S) (b x : B) (hx : x ∈ ordinaryIdealLinearSpan F S J) :
    b * x ∈ ordinaryIdealLinearSpan F S J := by
  have hle : ordinaryIdealLinearSpan F S J ≤
      (ordinaryIdealLinearSpan F S J).comap (leftProduct F b) := by
    apply Submodule.span_le.mpr
    rintro x ⟨u, hu, rfl⟩
    obtain ⟨c, s, hb⟩ := hsplit b
    change b * u.val ∈ ordinaryIdealLinearSpan F S J
    rw [hb, add_mul, smul_mul_assoc, one_mul]
    exact (ordinaryIdealLinearSpan F S J).add_mem
      ((ordinaryIdealLinearSpan F S J).smul_mem c (ordinaryIdealLinearSpan_mem F S J u hu))
      (ordinaryIdealLinearSpan_mem F S J (s * u) (J.mul_mem_left s u hu))
  exact hle hx

theorem ordinaryIdealLinearSpan_mul_right (S : NonUnitalSubalgebra F B)
    (hsplit : ∀ b : B, ∃ c : F, ∃ s : S, b = c • (1 : B) + s.val)
    (J : TwoSidedIdeal S) (x b : B) (hx : x ∈ ordinaryIdealLinearSpan F S J) :
    x * b ∈ ordinaryIdealLinearSpan F S J := by
  have hle : ordinaryIdealLinearSpan F S J ≤
      (ordinaryIdealLinearSpan F S J).comap (rightProduct F b) := by
    apply Submodule.span_le.mpr
    rintro x ⟨u, hu, rfl⟩
    obtain ⟨c, s, hb⟩ := hsplit b
    change u.val * b ∈ ordinaryIdealLinearSpan F S J
    rw [hb, mul_add, mul_smul_comm, mul_one]
    exact (ordinaryIdealLinearSpan F S J).add_mem
      ((ordinaryIdealLinearSpan F S J).smul_mem c (ordinaryIdealLinearSpan_mem F S J u hu))
      (ordinaryIdealLinearSpan_mem F S J (u * s) (J.mul_mem_right u s hu))
  exact hle hx

/-- A literal B-ideal obtained from an ordinary ideal of the non-unital S. -/
def ordinaryIdealLift (S : NonUnitalSubalgebra F B)
    (hsplit : ∀ b : B, ∃ c : F, ∃ s : S, b = c • (1 : B) + s.val)
    (J : TwoSidedIdeal S) : TwoSidedIdeal B :=
  TwoSidedIdeal.mk' (ordinaryIdealLinearSpan F S J : Set B)
    (ordinaryIdealLinearSpan F S J).zero_mem
    (fun hx hy => (ordinaryIdealLinearSpan F S J).add_mem hx hy)
    (fun hx => (ordinaryIdealLinearSpan F S J).neg_mem hx)
    (fun {b x} hx => ordinaryIdealLinearSpan_mul_left F S hsplit J b x hx)
    (fun {x b} hx => ordinaryIdealLinearSpan_mul_right F S hsplit J x b hx)

@[simp]
theorem mem_ordinaryIdealLift (S : NonUnitalSubalgebra F B)
    (hsplit : ∀ b : B, ∃ c : F, ∃ s : S, b = c • (1 : B) + s.val)
    (J : TwoSidedIdeal S) (x : B) :
    x ∈ ordinaryIdealLift F S hsplit J ↔ x ∈ ordinaryIdealLinearSpan F S J := by
  simp only [ordinaryIdealLift, TwoSidedIdeal.mem_mk']
  rfl

theorem ordinaryIdealLinearSpans_mul_zero (S : NonUnitalSubalgebra F B)
    (J K : TwoSidedIdeal S)
    (hprod : ∀ u : S, u ∈ J → ∀ v : S, v ∈ K → u * v = 0)
    (x y : B) (hx : x ∈ ordinaryIdealLinearSpan F S J)
    (hy : y ∈ ordinaryIdealLinearSpan F S K) : x * y = 0 := by
  refine Submodule.span_induction₂ (p := fun x y _ _ => x * y = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro x y ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact congrArg Subtype.val (hprod u hu v hv)
  · intro y hy
    exact zero_mul y
  · intro x hx
    exact mul_zero x
  · intro x y z hx hy hz hxy hyz
    rw [add_mul, hxy, hyz, zero_add]
  · intro x y z hx hy hz hxy hxz
    rw [mul_add, hxy, hxz, zero_add]
  · intro c x y hx hy hxy
    rw [smul_mul_assoc, hxy, smul_zero]
  · intro c x y hx hy hxy
    rw [mul_smul_comm, hxy, smul_zero]

theorem ordinaryIdeal_eq_bot_of_lift_eq_bot (S : NonUnitalSubalgebra F B)
    (hsplit : ∀ b : B, ∃ c : F, ∃ s : S, b = c • (1 : B) + s.val)
    (J : TwoSidedIdeal S) (hJ : ordinaryIdealLift F S hsplit J = ⊥) : J = ⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  have hmem : u.val ∈ ordinaryIdealLift F S hsplit J :=
    (mem_ordinaryIdealLift F S hsplit J u.val).mpr (ordinaryIdealLinearSpan_mem F S J u hu)
  rw [hJ] at hmem
  have hu0 : u.val = 0 := by simpa using hmem
  have heq : u = 0 := Subtype.ext hu0
  simpa using heq

/-- Ordinary non-unital primeness includes actual nonzeroness. -/
def OrdinaryNonUnitalPrime (A : Type*) [NonUnitalRing A] : Prop :=
  (∃ a : A, a ≠ 0) ∧ ∀ J K : TwoSidedIdeal A,
    (∀ x : A, x ∈ J → ∀ y : A, y ∈ K → x * y = 0) → J = ⊥ ∨ K = ⊥

theorem ordinaryPrime_of_scalar_positive_decomposition
    (S : NonUnitalSubalgebra F B) (hB : Actual.OrdinaryTwoSidedPrime B)
    (hsplit : ∀ b : B, ∃ c : F, ∃ s : S, b = c • (1 : B) + s.val)
    (hS : ∃ s : S, s ≠ 0) : OrdinaryNonUnitalPrime S := by
  refine ⟨hS, ?_⟩
  intro J K hprod
  have hprodB : ∀ x : B, x ∈ ordinaryIdealLift F S hsplit J →
      ∀ y : B, y ∈ ordinaryIdealLift F S hsplit K → x * y = 0 := by
    intro x hx y hy
    exact ordinaryIdealLinearSpans_mul_zero F S J K hprod x y
      ((mem_ordinaryIdealLift F S hsplit J x).mp hx)
      ((mem_ordinaryIdealLift F S hsplit K y).mp hy)
  rcases hB.2 (ordinaryIdealLift F S hsplit J) (ordinaryIdealLift F S hsplit K) hprodB with hJ | hK
  · exact Or.inl (ordinaryIdeal_eq_bot_of_lift_eq_bot F S hsplit J hJ)
  · exact Or.inr (ordinaryIdeal_eq_bot_of_lift_eq_bot F S hsplit K hK)

#print axioms CriticalGK2.PrimeInheritance.ordinaryIdealLinearSpans_mul_zero
#print axioms CriticalGK2.PrimeInheritance.ordinaryPrime_of_scalar_positive_decomposition

end

end CriticalGK2.PrimeInheritance
