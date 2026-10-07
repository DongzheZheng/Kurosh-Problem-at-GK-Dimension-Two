import CriticalGK2.LeadingDegree

/-!
# Actual highest-degree initial ideals

The degree-n piece is the actual image of J intersected with polynomials
of degree at most n. Its actual sum is proved to be a two-sided ideal and
homogeneous. Products of the initial ideals vanish modulo a homogeneous I
whenever products of the original ideals vanish modulo I.

Strictness is proved by choosing a shortest actual degree bound of an
element in J outside I. Removing its top component would lower that bound,
so the top component itself lies outside I.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

def initialDegreeComponent (J : TwoSidedIdeal (WordAlgebra F)) (n : ℕ) :
    Submodule F (WordAlgebra F) :=
  ((wordIdealSubmodule F J) ⊓ shortWordSubmodule F (n + 1)).map (degreeProjection F n)

def initialDegreeSubmodule (J : TwoSidedIdeal (WordAlgebra F)) : Submodule F (WordAlgebra F) :=
  ⨆ n : ℕ, initialDegreeComponent F J n

theorem initialDegreeComponent_le_homogeneous (J : TwoSidedIdeal (WordAlgebra F)) (n : ℕ) :
    initialDegreeComponent F J n ≤ homogeneous F n := by
  rintro P ⟨Q, hQ, rfl⟩
  exact degreeProjection_mem_homogeneous F n Q

theorem initialDegreeComponent_le_initialDegreeSubmodule
    (J : TwoSidedIdeal (WordAlgebra F)) (n : ℕ) :
    initialDegreeComponent F J n ≤ initialDegreeSubmodule F J := le_iSup _ n

theorem monomial_mul_initialDegreeSubmodule (J : TwoSidedIdeal (WordAlgebra F))
    (w : Word) (P : WordAlgebra F) (hP : P ∈ initialDegreeSubmodule F J) :
    MonoidAlgebra.single w 1 * P ∈ initialDegreeSubmodule F J := by
  let L : WordAlgebra F := MonoidAlgebra.single w 1
  have hL : L ∈ homogeneous F w.length := monomial_mem_homogeneous F w.length ⟨w, rfl⟩ 1
  have hLs : L ∈ shortWordSubmodule F (w.length + 1) := homogeneous_le_shortWordSubmodule F _ hL
  have hle : initialDegreeSubmodule F J ≤
      (initialDegreeSubmodule F J).comap (leftMultiplication F L) := by
    refine iSup_le fun n => ?_
    rintro x ⟨Q, hQ, rfl⟩
    change L * degreeProjection F n Q ∈ initialDegreeSubmodule F J
    have htop := degreeProjection_mul_top F w.length n L Q hLs hQ.2
    rw [degreeProjection_of_mem F w.length L hL] at htop
    rw [← htop]
    apply initialDegreeComponent_le_initialDegreeSubmodule F J (w.length + n)
    exact ⟨L * Q, ⟨J.mul_mem_left L Q hQ.1,
      shortWordSubmodule_mul F w.length n L Q hLs hQ.2⟩, rfl⟩
  exact hle hP

theorem initialDegreeSubmodule_mul_monomial (J : TwoSidedIdeal (WordAlgebra F))
    (w : Word) (P : WordAlgebra F) (hP : P ∈ initialDegreeSubmodule F J) :
    P * MonoidAlgebra.single w 1 ∈ initialDegreeSubmodule F J := by
  let L : WordAlgebra F := MonoidAlgebra.single w 1
  have hL : L ∈ homogeneous F w.length := monomial_mem_homogeneous F w.length ⟨w, rfl⟩ 1
  have hLs : L ∈ shortWordSubmodule F (w.length + 1) := homogeneous_le_shortWordSubmodule F _ hL
  have hle : initialDegreeSubmodule F J ≤
      (initialDegreeSubmodule F J).comap (rightMultiplication F L) := by
    refine iSup_le fun n => ?_
    rintro x ⟨Q, hQ, rfl⟩
    change degreeProjection F n Q * L ∈ initialDegreeSubmodule F J
    have htop := degreeProjection_mul_top F n w.length Q L hQ.2 hLs
    rw [degreeProjection_of_mem F w.length L hL] at htop
    rw [← htop]
    apply initialDegreeComponent_le_initialDegreeSubmodule F J (n + w.length)
    exact ⟨Q * L, ⟨J.mul_mem_right Q L hQ.1,
      shortWordSubmodule_mul F n w.length Q L hQ.2 hLs⟩, rfl⟩
  exact hle hP

theorem mul_initialDegreeSubmodule_mem (J : TwoSidedIdeal (WordAlgebra F))
    (a P : WordAlgebra F) (hP : P ∈ initialDegreeSubmodule F J) :
    a * P ∈ initialDegreeSubmodule F J := by
  classical
  have heq := MonoidAlgebra.lift_unique (AlgHom.id F (WordAlgebra F)) a
  change a = ∑ w ∈ a.support, a w • MonoidAlgebra.single w 1 at heq
  rw [heq, Finset.sum_mul]
  apply (initialDegreeSubmodule F J).sum_mem
  intro w hw
  rw [smul_mul_assoc]
  exact (initialDegreeSubmodule F J).smul_mem (a w)
    (monomial_mul_initialDegreeSubmodule F J w P hP)

theorem initialDegreeSubmodule_mul_mem (J : TwoSidedIdeal (WordAlgebra F))
    (P a : WordAlgebra F) (hP : P ∈ initialDegreeSubmodule F J) :
    P * a ∈ initialDegreeSubmodule F J := by
  classical
  have heq := MonoidAlgebra.lift_unique (AlgHom.id F (WordAlgebra F)) a
  change a = ∑ w ∈ a.support, a w • MonoidAlgebra.single w 1 at heq
  rw [heq, Finset.mul_sum]
  apply (initialDegreeSubmodule F J).sum_mem
  intro w hw
  rw [mul_smul_comm]
  exact (initialDegreeSubmodule F J).smul_mem (a w)
    (initialDegreeSubmodule_mul_monomial F J w P hP)

/-- Actual initial ideal; its two-sided closure has been proved above. -/
def initialDegreeIdeal (J : TwoSidedIdeal (WordAlgebra F)) : TwoSidedIdeal (WordAlgebra F) :=
  TwoSidedIdeal.mk' (initialDegreeSubmodule F J : Set (WordAlgebra F))
    (initialDegreeSubmodule F J).zero_mem
    (fun hP hQ => (initialDegreeSubmodule F J).add_mem hP hQ)
    (fun hP => (initialDegreeSubmodule F J).neg_mem hP)
    (fun {a P} hP => mul_initialDegreeSubmodule_mem F J a P hP)
    (fun {P a} hP => initialDegreeSubmodule_mul_mem F J P a hP)

@[simp]
theorem mem_initialDegreeIdeal (J : TwoSidedIdeal (WordAlgebra F)) (P : WordAlgebra F) :
    P ∈ initialDegreeIdeal F J ↔ P ∈ initialDegreeSubmodule F J := by
  simp only [initialDegreeIdeal, TwoSidedIdeal.mem_mk']
  rfl

theorem initialDegreeIdeal_homogeneous (J : TwoSidedIdeal (WordAlgebra F)) :
    WordIdealHomogeneous F (initialDegreeIdeal F J) := by
  intro n P hP
  apply (mem_initialDegreeIdeal F J _).mpr
  have hle : initialDegreeSubmodule F J ≤
      (initialDegreeSubmodule F J).comap (degreeProjection F n) := by
    refine iSup_le fun m => ?_
    intro Q hQ
    change degreeProjection F n Q ∈ initialDegreeSubmodule F J
    have hQm := initialDegreeComponent_le_homogeneous F J m hQ
    by_cases hmn : m = n
    · rw [← hmn, degreeProjection_of_mem F m Q hQm]
      exact initialDegreeComponent_le_initialDegreeSubmodule F J m hQ
    · rw [degreeProjection_of_other_degree F m n hmn Q hQm]
      exact (initialDegreeSubmodule F J).zero_mem
  exact hle ((mem_initialDegreeIdeal F J P).mp hP)

/-- A homogeneous initial ideal I remains included when taking initial
degree parts of any actual ideal J that contains I. -/
theorem le_initialDegreeIdeal (I J : TwoSidedIdeal (WordAlgebra F))
    (hhomI : WordIdealHomogeneous F I) (hIJ : I ≤ J) : I ≤ initialDegreeIdeal F J := by
  classical
  intro P hP
  apply (mem_initialDegreeIdeal F J P).mpr
  rw [← sum_homogeneousProjection_eq F P]
  apply (initialDegreeSubmodule F J).sum_mem
  intro n hn
  let Q := degreeProjection F n P
  have hQn : Q ∈ homogeneous F n := degreeProjection_mem_homogeneous F n P
  apply initialDegreeComponent_le_initialDegreeSubmodule F J n
  exact ⟨Q, ⟨hIJ (hhomI n P hP), homogeneous_le_shortWordSubmodule F n hQn⟩,
    degreeProjection_of_mem F n Q hQn⟩

/-- A least actual bound of an element outside I has a top component outside
I. This provides strictness of the initial ideal without a leading-term
existence assumption. -/
theorem initialDegreeIdeal_not_le_of_not_le
    (I J : TwoSidedIdeal (WordAlgebra F)) (hIJ : I ≤ J) (hnot : ¬ J ≤ I) :
    ¬ initialDegreeIdeal F J ≤ I := by
  classical
  have hex : ∃ P : WordAlgebra F, P ∈ J ∧ P ∉ I := by
    by_contra h
    apply hnot
    intro P hPJ
    by_contra hPI
    exact h ⟨P, hPJ, hPI⟩
  have hbound : ∃ n : ℕ, ∃ P : WordAlgebra F,
      P ∈ J ∧ P ∈ shortWordSubmodule F (n + 1) ∧ P ∉ I := by
    obtain ⟨P, hPJ, hPI⟩ := hex
    obtain ⟨n, hn⟩ := exists_mem_shortWordSubmodule F P
    exact ⟨n, P, hPJ, hn, hPI⟩
  let n := Nat.find hbound
  obtain ⟨P, hPJ, hPs, hPI⟩ := Nat.find_spec hbound
  have htop : degreeProjection F n P ∉ I := by
    intro hpI
    let Q := P - degreeProjection F n P
    have hQJ : Q ∈ J := J.sub_mem hPJ (hIJ hpI)
    have hQs : Q ∈ shortWordSubmodule F n := sub_degreeProjection_mem_short F n P hPs
    have hQI : Q ∉ I := by
      intro hQ
      apply hPI
      have hsum := I.add_mem hQ hpI
      simpa only [Q, sub_add_cancel] using hsum
    by_cases hn : n = 0
    · have hQ0 : Q = 0 := shortWordSubmodule_zero F Q (hn ▸ hQs)
      apply hQI
      rw [hQ0]
      exact I.zero_mem
    · have hpred : n - 1 + 1 = n := by omega
      have hcandidate : ∃ Q : WordAlgebra F,
          Q ∈ J ∧ Q ∈ shortWordSubmodule F ((n - 1) + 1) ∧ Q ∉ I :=
        ⟨Q, hQJ, hpred.symm ▸ hQs, hQI⟩
      have hmin : n ≤ n - 1 := Nat.find_min' hbound hcandidate
      omega
  intro hle
  apply htop
  apply hle
  apply (mem_initialDegreeIdeal F J _).mpr
  exact initialDegreeComponent_le_initialDegreeSubmodule F J n
    ⟨P, ⟨hPJ, hPs⟩, rfl⟩

theorem initialDegreeIdeals_mul_mem_of_original_mul_mem
    (I J K : TwoSidedIdeal (WordAlgebra F)) (hhomI : WordIdealHomogeneous F I)
    (hprod : ∀ P : WordAlgebra F, P ∈ J → ∀ Q : WordAlgebra F, Q ∈ K → P * Q ∈ I)
    (P Q : WordAlgebra F) (hP : P ∈ initialDegreeIdeal F J)
    (hQ : Q ∈ initialDegreeIdeal F K) : P * Q ∈ I := by
  let U := wordIdealSubmodule F I
  have hle : initialDegreeSubmodule F J ≤ U.comap (rightMultiplication F Q) := by
    refine iSup_le fun m => ?_
    intro x hx
    have hK : initialDegreeSubmodule F K ≤ U.comap (leftMultiplication F x) := by
      refine iSup_le fun n => ?_
      rintro y ⟨B, hB, rfl⟩
      obtain ⟨A, hA, rfl⟩ := hx
      change degreeProjection F m A * degreeProjection F n B ∈ I
      rw [← degreeProjection_mul_top F m n A B hA.2 hB.2]
      exact hhomI (m + n) (A * B) (hprod A hA.1 B hB.1)
    exact hK ((mem_initialDegreeIdeal F K Q).mp hQ)
  exact hle ((mem_initialDegreeIdeal F J P).mp hP)

#print axioms CriticalGK2.Actual.initialDegreeIdeal_homogeneous
#print axioms CriticalGK2.Actual.le_initialDegreeIdeal
#print axioms CriticalGK2.Actual.initialDegreeIdeal_not_le_of_not_le
#print axioms CriticalGK2.Actual.initialDegreeIdeals_mul_mem_of_original_mul_mem

end

end CriticalGK2.Actual
