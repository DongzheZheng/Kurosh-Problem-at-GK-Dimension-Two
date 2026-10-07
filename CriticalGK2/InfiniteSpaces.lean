import CriticalGK2.StagedSpaces

/-!
# The actual infinite homogeneous family

Every natural dyadic height belongs to a unique finite stage. The family is
assembled at their literal common endpoints. Nonzero spaces and all global
coherence edges are proved from the polynomial constructors.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F] (waiting size : ℕ → ℕ)

theorem exists_stage_end_above (n : ℕ) :
    ∃ j : ℕ, n < stageHeight F waiting size (j + 1) := by
  refine ⟨n, ?_⟩
  have h := index_le_stageHeight F waiting size (n + 1)
  omega

def activeStage (n : ℕ) : ℕ := Nat.find (exists_stage_end_above F waiting size n)

theorem activeStage_upper (n : ℕ) :
    n < stageHeight F waiting size (activeStage F waiting size n + 1) :=
  Nat.find_spec (exists_stage_end_above F waiting size n)

theorem activeStage_lower (n : ℕ) :
    stageHeight F waiting size (activeStage F waiting size n) ≤ n := by
  cases he : activeStage F waiting size n with
  | zero => simp [he]
  | succ j =>
    have hj : j < activeStage F waiting size n := by omega
    have hnot := Nat.find_min (exists_stage_end_above F waiting size n) hj
    change ¬ n < stageHeight F waiting size (j + 1) at hnot
    simpa only [he] using Nat.le_of_not_gt hnot

theorem activeStage_eq (n j : ℕ)
    (hlo : stageHeight F waiting size j ≤ n)
    (hhi : n < stageHeight F waiting size (j + 1)) :
    activeStage F waiting size n = j := by
  apply Nat.le_antisymm
  · exact Nat.find_min' (exists_stage_end_above F waiting size n) hhi
  · by_contra h
    have hj : activeStage F waiting size n < j := by omega
    have hm := (stageHeight_strictMono F waiting size).monotone
      (Nat.succ_le_of_lt hj)
    simp only [Nat.succ_eq_add_one] at hm
    have hu := activeStage_upper F waiting size n
    omega

/-- A literal actual space at every dyadic height. -/
def infiniteSpace (n : ℕ) : Submodule F (WordAlgebra F) :=
  stageSpace F (stagePrefix F waiting size (activeStage F waiting size n))
    (size (activeStage F waiting size n)) (waiting (activeStage F waiting size n))
    (n - stageHeight F waiting size (activeStage F waiting size n))

theorem infiniteSpace_at_stage (j a : ℕ)
    (ha : a ≤ waiting j + operationHeight (size j)) :
    infiniteSpace F waiting size (stageHeight F waiting size j + a) =
      stageSpace F (stagePrefix F waiting size j) (size j) (waiting j) a := by
  by_cases he : a = waiting j + operationHeight (size j)
  · subst a
    have hn : stageHeight F waiting size j +
        (waiting j + operationHeight (size j)) = stageHeight F waiting size (j + 1) := by
      rw [stageHeight_succ]
      omega
    rw [hn]
    have hj := activeStage_eq F waiting size (stageHeight F waiting size (j + 1)) (j + 1)
      le_rfl (stageHeight_lt_succ F waiting size (j + 1))
    simp only [infiniteSpace, hj, Nat.sub_self]
    exact (stageSpace_matches_next F waiting size j).symm
  · have hlt : a < waiting j + operationHeight (size j) := by omega
    have hhi : stageHeight F waiting size j + a < stageHeight F waiting size (j + 1) := by
      rw [stageHeight_succ]
      omega
    have hj := activeStage_eq F waiting size (stageHeight F waiting size j + a) j
      (Nat.le_add_right _ _) hhi
    simp only [infiniteSpace, hj, Nat.add_sub_cancel_left]

theorem infiniteSpace_le_homogeneous (n : ℕ) :
    infiniteSpace F waiting size n ≤ homogeneous F (2 ^ n) := by
  let j := activeStage F waiting size n
  have hlo := activeStage_lower F waiting size n
  change stageHeight F waiting size j ≤ n at hlo
  have hn : (stagePrefix F waiting size j).height +
      (n - stageHeight F waiting size j) = n := by
    change stageHeight F waiting size j + (n - stageHeight F waiting size j) = n
    omega
  simpa only [infiniteSpace, hn, j] using
    stageSpace_le_homogeneous F (stagePrefix F waiting size j) (size j) (waiting j)
      (n - stageHeight F waiting size j)

theorem infiniteSpace_ne_bot (n : ℕ) : infiniteSpace F waiting size n ≠ ⊥ :=
  stageSpace_ne_bot F _ _ _ _

/-- Global coherence includes all stage boundaries. -/
theorem infiniteSpace_coherent (n : ℕ) :
    infiniteSpace F waiting size (n + 1) ≤
      productSpan F (infiniteSpace F waiting size n) (infiniteSpace F waiting size n) := by
  let j := activeStage F waiting size n
  let a := n - stageHeight F waiting size j
  have hlo := activeStage_lower F waiting size n
  have hhi := activeStage_upper F waiting size n
  change stageHeight F waiting size j ≤ n at hlo
  change n < stageHeight F waiting size (j + 1) at hhi
  have hn : stageHeight F waiting size j + a = n := by dsimp only [a]; omega
  have ha : a < waiting j + operationHeight (size j) := by
    have hs := stageHeight_succ F waiting size j
    omega
  have hn1 : stageHeight F waiting size j + (a + 1) = n + 1 := by omega
  rw [← hn1, infiniteSpace_at_stage F waiting size j (a + 1) (by omega)]
  rw [← hn, infiniteSpace_at_stage F waiting size j a (by omega)]
  exact stageSpace_coherent F _ _ _ _ ha

/-- The actual PI endpoint occurs in the infinite family at each completed
stage and is killed by every commutative-coefficient matrix evaluation. -/
theorem infiniteSpace_stage_endpoint_killed (C : Type*) [CommRing C] [Algebra F C]
    (j : ℕ) (f : WordAlgebra F →ₐ[F] Matrix (Fin (size j)) (Fin (size j)) C) :
    infiniteSpace F waiting size (stageHeight F waiting size (j + 1)) ≤
      LinearMap.ker f.toLinearMap := by
  have hj := infiniteSpace_at_stage F waiting size j
    (waiting j + operationHeight (size j)) le_rfl
  have hn : stageHeight F waiting size j +
      (waiting j + operationHeight (size j)) = stageHeight F waiting size (j + 1) := by
    rw [stageHeight_succ]
    omega
  rw [hn, stageSpace_endpoint] at hj
  rw [hj]
  exact resetPrefix_space_killed F C _ _ f

end

end CriticalGK2.Actual
