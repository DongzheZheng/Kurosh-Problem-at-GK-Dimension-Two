import Mathlib.Data.List.Infix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# An actual infinite word in an unbounded binary prefix language

The ordinary input is an actual set of finite Boolean lists, closed under
prefixes, with an actual member at every length.  The recursion chooses a
letter only after proving that one of the two children still has arbitrarily
long extensions. The resulting function `ℕ -> Bool` has every
`List.ofFn` prefix in the given language.

For a factorial language the same construction supplies every actual shifted
finite factor.  Connecting a normal-word language of the algebra quotient to
these inputs is handled by the normal-language lemmas.
-/

namespace CriticalGK2.Language

noncomputable section

/-- Every prefix of a language word remains in the actual language. -/
def PrefixClosed (L : Set (List Bool)) : Prop :=
  ∀ ⦃u v : List Bool⦄, u <+: v → v ∈ L → u ∈ L

/-- Every contiguous factor of a language word remains in the actual language. -/
def FactorClosed (L : Set (List Bool)) : Prop :=
  ∀ ⦃u v : List Bool⦄, u <:+: v → v ∈ L → u ∈ L

/-- Actual extensions of this particular word exist at arbitrarily large
lengths. -/
def UnboundedExtensions (L : Set (List Bool)) (u : List Bool) : Prop :=
  ∀ N : ℕ, ∃ v : List Bool, u <+: v ∧ v ∈ L ∧ N ≤ v.length

/-- Finite binary branching: if both children had a finite obstruction
threshold, their maximum would obstruct arbitrarily long parent extensions. -/
theorem exists_unbounded_child (L : Set (List Bool)) (u : List Bool)
    (hu : UnboundedExtensions L u) :
    ∃ b : Bool, UnboundedExtensions L (u ++ [b]) := by
  classical
  by_contra h
  have hnot : ∀ b : Bool, ¬ UnboundedExtensions L (u ++ [b]) := not_exists.mp h
  obtain ⟨N₀, hN₀⟩ := not_forall.mp (hnot false)
  obtain ⟨N₁, hN₁⟩ := not_forall.mp (hnot true)
  obtain ⟨v, huv, hv, hlen⟩ := hu (max N₀ N₁ + u.length + 1)
  have h₀ : N₀ ≤ max N₀ N₁ := le_max_left _ _
  have h₁ : N₁ ≤ max N₀ N₁ := le_max_right _ _
  have hlt : u.length < v.length := by omega
  have hchild := List.concat_get_prefix huv hlt
  cases hb : v.get ⟨u.length, hlt⟩ with
  | false =>
      apply hN₀
      exact ⟨v, by simpa only [hb] using hchild, hv, by omega⟩
  | true =>
      apply hN₁
      exact ⟨v, by simpa only [hb] using hchild, hv, by omega⟩

/-- A chosen actual child letter, chosen from the theorem above. -/
def unboundedChildLetter (L : Set (List Bool))
    (u : {u : List Bool // UnboundedExtensions L u}) : Bool :=
  Classical.choose (exists_unbounded_child L u.val u.property)

theorem unboundedChildLetter_property (L : Set (List Bool))
    (u : {u : List Bool // UnboundedExtensions L u}) :
    UnboundedExtensions L (u.val ++ [unboundedChildLetter L u]) :=
  Classical.choose_spec (exists_unbounded_child L u.val u.property)

/-- One step preserves the directly quantified extension predicate. -/
def unboundedChildWord (L : Set (List Bool))
    (u : {u : List Bool // UnboundedExtensions L u}) :
    {u : List Bool // UnboundedExtensions L u} :=
  ⟨u.val ++ [unboundedChildLetter L u], unboundedChildLetter_property L u⟩

/-- An actual natural-number recursion of finite lists. -/
def unboundedWordPath (L : Set (List Bool)) (hroot : UnboundedExtensions L []) :
    ℕ → {u : List Bool // UnboundedExtensions L u}
  | 0 => ⟨[], hroot⟩
  | n + 1 => unboundedChildWord L (unboundedWordPath L hroot n)

/-- The actual infinite sequence consists of the chosen successive letters. -/
def unboundedWordStream (L : Set (List Bool)) (hroot : UnboundedExtensions L []) :
    ℕ → Bool := fun n => unboundedChildLetter L (unboundedWordPath L hroot n)

/-- A literal finite prefix of an actual stream. -/
def streamPrefix (x : ℕ → Bool) (n : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => x i.val)

/-- A literal contiguous factor, starting at the specified position. -/
def streamFactor (x : ℕ → Bool) (s n : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => x (s + i.val))

@[simp]
theorem streamPrefix_length (x : ℕ → Bool) (n : ℕ) :
    (streamPrefix x n).length = n := List.length_ofFn

@[simp]
theorem streamFactor_length (x : ℕ → Bool) (s n : ℕ) :
    (streamFactor x s n).length = n := List.length_ofFn

theorem streamPrefix_succ (x : ℕ → Bool) (n : ℕ) :
    streamPrefix x (n + 1) = streamPrefix x n ++ [x n] := by
  exact List.ofFn_succ_last

/-- The list obtained by taking actual stream coordinates is exactly the
list constructed by the proved child recursion. -/
theorem streamPrefix_unboundedWordStream (L : Set (List Bool))
    (hroot : UnboundedExtensions L []) (n : ℕ) :
    streamPrefix (unboundedWordStream L hroot) n = (unboundedWordPath L hroot n).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [streamPrefix_succ, ih]
      rfl

theorem unboundedExtensions_mem (L : Set (List Bool)) (hL : PrefixClosed L)
    (u : List Bool) (hu : UnboundedExtensions L u) : u ∈ L := by
  obtain ⟨v, huv, hv, _⟩ := hu 0
  exact hL huv hv

theorem empty_unboundedExtensions_of_every_length (L : Set (List Bool))
    (hwords : ∀ n : ℕ, ∃ u : List Bool, u ∈ L ∧ u.length = n) :
    UnboundedExtensions L [] := by
  intro n
  obtain ⟨u, hu, hlen⟩ := hwords n
  exact ⟨u, List.nil_prefix, hu, hlen.ge⟩

/-- Every unbounded binary prefix language contains the prefixes of an
infinite binary word. -/
theorem exists_stream_prefix_mem (L : Set (List Bool)) (hL : PrefixClosed L)
    (hwords : ∀ n : ℕ, ∃ u : List Bool, u ∈ L ∧ u.length = n) :
    ∃ x : ℕ → Bool, ∀ n : ℕ, streamPrefix x n ∈ L := by
  let hroot := empty_unboundedExtensions_of_every_length L hwords
  refine ⟨unboundedWordStream L hroot, ?_⟩
  intro n
  rw [streamPrefix_unboundedWordStream]
  exact unboundedExtensions_mem L hL _ (unboundedWordPath L hroot n).property

/-- The actual longer prefix splits into the specified initial prefix and
the actual shifted factor. -/
theorem streamPrefix_add (x : ℕ → Bool) (s n : ℕ) :
    streamPrefix x (s + n) = streamPrefix x s ++ streamFactor x s n := by
  exact List.ofFn_add

theorem streamFactor_infix_prefix (x : ℕ → Bool) (s n : ℕ) :
    streamFactor x s n <:+: streamPrefix x (s + n) := by
  rw [streamPrefix_add]
  exact List.infix_append_right

/-- For a factorial actual language, every actual factor of the constructed
stream belongs to the language. -/
theorem exists_stream_factors_mem (L : Set (List Bool)) (hL : FactorClosed L)
    (hwords : ∀ n : ℕ, ∃ u : List Bool, u ∈ L ∧ u.length = n) :
    ∃ x : ℕ → Bool, ∀ s n : ℕ, streamFactor x s n ∈ L := by
  have hprefix : PrefixClosed L := by
    intro u v h hv
    exact hL h.isInfix hv
  obtain ⟨x, hx⟩ := exists_stream_prefix_mem L hprefix hwords
  exact ⟨x, fun s n => hL (streamFactor_infix_prefix x s n) (hx (s + n))⟩

#print axioms CriticalGK2.Language.exists_unbounded_child
#print axioms CriticalGK2.Language.exists_stream_prefix_mem
#print axioms CriticalGK2.Language.exists_stream_factors_mem

end

end CriticalGK2.Language
