import CriticalGK2.HomogeneousIdealZorn

/-!
# Actual highest-degree projection and actual multiplication

All bounds and projections are literal coefficient conditions on the free
word algebra. The highest-degree product identity is proved on actual word
monomials and extended by finite linear span induction.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- The actual degree projection, with ambient word-algebra codomain. -/
def degreeProjection (n : ℕ) : WordAlgebra F →ₗ[F] WordAlgebra F :=
  (homogeneous F n).subtype.comp (homogeneousProjection F n)

@[simp]
theorem degreeProjection_apply (n : ℕ) (P : WordAlgebra F) :
    degreeProjection F n P = (homogeneousProjection F n P).val := rfl

theorem degreeProjection_of_mem (n : ℕ) (P : WordAlgebra F)
    (hP : P ∈ homogeneous F n) : degreeProjection F n P = P :=
  homogeneousProjection_of_mem F n P hP

theorem degreeProjection_of_other_degree (m n : ℕ) (hmn : m ≠ n)
    (P : WordAlgebra F) (hP : P ∈ homogeneous F m) : degreeProjection F n P = 0 :=
  homogeneousProjection_of_other_degree F m n hmn P hP

theorem degreeProjection_mem_homogeneous (n : ℕ) (P : WordAlgebra F) :
    degreeProjection F n P ∈ homogeneous F n := (homogeneousProjection F n P).property

theorem degreeProjection_single (n : ℕ) (w : Word) :
    degreeProjection F n (MonoidAlgebra.single w 1) =
      if w.length = n then MonoidAlgebra.single w 1 else 0 := by
  by_cases hw : w.length = n
  · rw [if_pos hw]
    exact degreeProjection_of_mem F n _
      (monomial_mem_homogeneous F n ⟨w, hw⟩ 1)
  · rw [if_neg hw]
    exact degreeProjection_of_other_degree F w.length n hw _
      (monomial_mem_homogeneous F w.length ⟨w, rfl⟩ 1)

theorem homogeneous_le_shortWordSubmodule (n : ℕ) :
    homogeneous F n ≤ shortWordSubmodule F (n + 1) := by
  intro P hP
  change ∀ w ∈ P.support, w.length = n at hP
  change ∀ w ∈ P.support, w.length < n + 1
  intro w hw
  rw [hP w hw]
  omega

theorem shortWordSubmodule_mul (m n : ℕ) (P Q : WordAlgebra F)
    (hP : P ∈ shortWordSubmodule F (m + 1))
    (hQ : Q ∈ shortWordSubmodule F (n + 1)) :
    P * Q ∈ shortWordSubmodule F (m + n + 1) := by
  classical
  change ∀ w ∈ (P * Q).support, w.length < m + n + 1
  intro w hw
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp (MonoidAlgebra.support_mul P Q hw)
  have hum : u.length < m + 1 := hP hu
  have hvn : v.length < n + 1 := hQ hv
  rw [FreeMonoid.length_mul]
  omega

/-- The true highest-degree multiplication identity for actual bounded words. -/
theorem degreeProjection_mul_top (m n : ℕ) (P Q : WordAlgebra F)
    (hP : P ∈ shortWordSubmodule F (m + 1))
    (hQ : Q ∈ shortWordSubmodule F (n + 1)) :
    degreeProjection F (m + n) (P * Q) =
      degreeProjection F m P * degreeProjection F n Q := by
  classical
  have hP' : P ∈ Submodule.span F
      ((fun w : Word => MonoidAlgebra.single w (1 : F)) '' {w : Word | w.length < m + 1}) := by
    change P ∈ Finsupp.supported F F {w : Word | w.length < m + 1} at hP
    rw [Finsupp.supported_eq_span_single] at hP
    exact hP
  have hQ' : Q ∈ Submodule.span F
      ((fun w : Word => MonoidAlgebra.single w (1 : F)) '' {w : Word | w.length < n + 1}) := by
    change Q ∈ Finsupp.supported F F {w : Word | w.length < n + 1} at hQ
    rw [Finsupp.supported_eq_span_single] at hQ
    exact hQ
  refine Submodule.span_induction₂
    (p := fun P Q _ _ => degreeProjection F (m + n) (P * Q) =
      degreeProjection F m P * degreeProjection F n Q) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hP' hQ'
  · rintro P Q ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    change u.length < m + 1 at hu
    change v.length < n + 1 at hv
    rw [MonoidAlgebra.single_mul_single, one_mul, degreeProjection_single,
      degreeProjection_single, degreeProjection_single]
    by_cases hum : u.length = m <;> by_cases hvn : v.length = n
    · have huv : (u * v).length = m + n := by simp only [FreeMonoid.length_mul, hum, hvn]
      simp only [if_pos huv, if_pos hum, if_pos hvn, MonoidAlgebra.single_mul_single, one_mul]
    · have huv : (u * v).length ≠ m + n := by rw [FreeMonoid.length_mul]; omega
      simp only [if_neg huv, if_pos hum, if_neg hvn, mul_zero]
    · have huv : (u * v).length ≠ m + n := by rw [FreeMonoid.length_mul]; omega
      simp only [if_neg huv, if_neg hum, if_pos hvn, zero_mul]
    · have huv : (u * v).length ≠ m + n := by rw [FreeMonoid.length_mul]; omega
      simp only [if_neg huv, if_neg hum, if_neg hvn, zero_mul]
  · intro Q hQ
    simp only [zero_mul, map_zero]
  · intro P hP
    simp only [mul_zero, map_zero]
  · intro P Q R hP hQ hR hPR hQR
    simp only [add_mul, map_add, hPR, hQR]
  · intro P Q R hP hQ hR hPQ hPR
    simp only [mul_add, map_add, hPQ, hPR]
  · intro c P Q hP hQ hPQ
    simp only [smul_mul_assoc, map_smul, hPQ]
  · intro c P Q hP hQ hPQ
    simp only [mul_smul_comm, map_smul, hPQ]

/-- Removing the actual top degree lowers the actual coefficient bound. -/
theorem sub_degreeProjection_mem_short (n : ℕ) (P : WordAlgebra F)
    (hP : P ∈ shortWordSubmodule F (n + 1)) :
    P - degreeProjection F n P ∈ shortWordSubmodule F n := by
  change P - degreeProjection F n P ∈ Finsupp.supported F F {w : Word | w.length < n}
  apply (Finsupp.mem_supported' (s := {w : Word | w.length < n}) F
    (P - degreeProjection F n P)).mpr
  intro w hw
  change ¬ w.length < n at hw
  change P w - (homogeneousProjection F n P).val w = 0
  rw [homogeneousProjection_coeff]
  by_cases hwn : w.length = n
  · rw [if_pos hwn, sub_self]
  · rw [if_neg hwn, sub_zero]
    have hnot : ¬ w.length < n + 1 := by omega
    exact (Finsupp.mem_supported' (s := {w : Word | w.length < n + 1}) F P).mp hP w hnot

theorem shortWordSubmodule_zero (P : WordAlgebra F) (hP : P ∈ shortWordSubmodule F 0) :
    P = 0 := by
  apply Finsupp.ext
  intro w
  change P w = (0 : F)
  exact (Finsupp.mem_supported' (s := {w : Word | w.length < 0}) F P).mp hP w
    (by change ¬ w.length < 0; exact Nat.not_lt_zero _)

/-- Every actual polynomial has an actual finite coefficient-degree bound. -/
theorem exists_mem_shortWordSubmodule (P : WordAlgebra F) :
    ∃ n : ℕ, P ∈ shortWordSubmodule F (n + 1) := by
  classical
  refine ⟨(MonoidAlgebra.coeff P).support.sup (fun w : Word => w.length), ?_⟩
  change ∀ w ∈ (MonoidAlgebra.coeff P).support,
    w.length < (MonoidAlgebra.coeff P).support.sup (fun w : Word => w.length) + 1
  intro w hw
  exact Nat.lt_succ_of_le (Finset.le_sup hw)

#print axioms CriticalGK2.Actual.degreeProjection_mul_top
#print axioms CriticalGK2.Actual.sub_degreeProjection_mem_short

end

end CriticalGK2.Actual
