import CriticalGK2.AllCutClosure

/-!
# Actual homogeneous projections and the actual all-cut direct sum

The maps are actual coefficient filters in the actual free algebra.  Their
delta behavior on every actual homogeneous submodule proves the equality
E ∩ H_n = E_n.  This is needed before nonzeroness of the separate component
quotients can be transferred to the actual ring quotient.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F]

/-- The actual degree-n coefficient projection. -/
def homogeneousProjection (n : ℕ) : WordAlgebra F →ₗ[F] homogeneous F n := by
  classical
  exact Finsupp.restrictDom F F (wordsOfLength n)

@[simp]
theorem homogeneousProjection_coeff (n : ℕ) (x : WordAlgebra F) (w : Word) :
    (homogeneousProjection F n x).val w = if w.length = n then x w else 0 := by
  classical
  change (Finsupp.filter (fun w : Word => w ∈ wordsOfLength n)
    (MonoidAlgebra.coeff x)) w = if w.length = n then x w else 0
  rw [Finsupp.filter_apply]
  by_cases hw : w.length = n
  · have hw' : w ∈ wordsOfLength n := hw
    rw [if_pos hw', if_pos hw]
    all_goals rfl
  · have hw' : w ∉ wordsOfLength n := hw
    rw [if_neg hw', if_neg hw]

theorem homogeneousProjection_of_mem (n : ℕ) (x : WordAlgebra F)
    (hx : x ∈ homogeneous F n) : (homogeneousProjection F n x).val = x := by
  apply Finsupp.ext
  intro w
  rw [homogeneousProjection_coeff]
  by_cases hw : w.length = n
  · simp [hw]
  · have hxw := (mem_homogeneous_iff F n x).mp hx w hw
    simp [hw, hxw]

/-- Delta behavior on another homogeneous degree. -/
theorem homogeneousProjection_of_other_degree (m n : ℕ) (hmn : m ≠ n)
    (x : WordAlgebra F) (hx : x ∈ homogeneous F m) :
    (homogeneousProjection F n x).val = 0 := by
  apply Finsupp.ext
  intro w
  change (homogeneousProjection F n x).val w = (0 : F)
  rw [homogeneousProjection_coeff]
  by_cases hwn : w.length = n
  · have hwm : w.length ≠ m := fun hwm => hmn (hwm.symm.trans hwn)
    have hxw := (mem_homogeneous_iff F m x).mp hx w hwm
    simp [hwn, hxw]
  · simp [hwn]

theorem allCutComponent_le_allCutSubmodule (W : DyadicDualData F) (n : ℕ) :
    allCutComponent F W n ≤ allCutSubmodule F W := by
  cases n with
  | zero => simp [allCutComponent_zero]
  | succ n =>
      exact le_iSup (fun m => allCutComponent F W (m + 1)) n

/-- Each actual component projection sends the actual sum E into its
same-degree component E_n.  Membership in the sum is handled by the lattice
universal property, without supposing ideal closure. -/
theorem homogeneousProjection_allCutSubmodule_mem (W : DyadicDualData F) (n : ℕ)
    (x : WordAlgebra F) (hx : x ∈ allCutSubmodule F W) :
    (homogeneousProjection F n x).val ∈ allCutComponent F W n := by
  let p : WordAlgebra F →ₗ[F] WordAlgebra F :=
    (homogeneous F n).subtype.comp (homogeneousProjection F n)
  have hle : allCutSubmodule F W ≤ (allCutComponent F W n).comap p := by
    apply iSup_le
    intro m y hy
    change (homogeneousProjection F n y).val ∈ allCutComponent F W n
    have hyH := allCutComponent_le_homogeneous F W (m + 1) hy
    by_cases hmn : m + 1 = n
    · have hyn : y ∈ homogeneous F n := hmn ▸ hyH
      rw [homogeneousProjection_of_mem F n y hyn]
      exact hmn ▸ hy
    · rw [homogeneousProjection_of_other_degree F (m + 1) n hmn y hyH]
      exact (allCutComponent F W n).zero_mem
  exact hle hx

/-- Genuine equality in the actual ambient free-algebra submodule lattice. -/
theorem allCutSubmodule_inf_homogeneous (W : DyadicDualData F) (n : ℕ) :
    allCutSubmodule F W ⊓ homogeneous F n = allCutComponent F W n := by
  apply le_antisymm
  · intro x hx
    have hp := homogeneousProjection_allCutSubmodule_mem F W n x hx.1
    rw [homogeneousProjection_of_mem F n x hx.2] at hp
    exact hp
  · exact le_inf (allCutComponent_le_allCutSubmodule F W n)
      (allCutComponent_le_homogeneous F W n)

/-- Exact intersection inside the actual degree-n subtype, which is the
input needed to connect its quotient with the actual ring quotient. -/
theorem allCutSubmodule_comap_homogeneous (W : DyadicDualData F) (n : ℕ) :
    (allCutSubmodule F W).comap (homogeneous F n).subtype =
      (allCutComponent F W n).comap (homogeneous F n).subtype := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    have hp := homogeneousProjection_allCutSubmodule_mem F W n x.val hx
    rw [homogeneousProjection_of_mem F n x.val x.property] at hp
    exact hp
  · intro hx
    exact allCutComponent_le_allCutSubmodule F W n hx

end

end CriticalGK2.Actual
