import CriticalGK2.WordConsumption

namespace CriticalGK2.Automaton

def afterConsume {R : Type*} [Zero R] (p w : List Bool) (f : List Bool → R) : R :=
  match consumePrefix p w with
  | none => 0
  | some t => f t

@[simp]
theorem afterConsume_nil {R : Type*} [Zero R] (w : List Bool) (f : List Bool → R) :
    afterConsume [] w f = f w := rfl

theorem afterConsume_of_some {R : Type*} [Zero R] (p w t : List Bool)
    (h : consumePrefix p w = some t) (f : List Bool → R) :
    afterConsume p w f = f t := by simp [afterConsume, h]

theorem afterConsume_of_none {R : Type*} [Zero R] (p w : List Bool)
    (h : consumePrefix p w = none) (f : List Bool → R) :
    afterConsume p w f = 0 := by simp [afterConsume, h]

/-- The coefficient of an actual word in an actual left-monomial product
is determined by exact residual consumption. -/
theorem single_word_mul_coefficient {R : Type*} [CommRing R]
    (p w : List Bool) (c : R) (P : MonoidAlgebra R (FreeMonoid Bool)) :
    (MonoidAlgebra.single (FreeMonoid.ofList p) c * P) (FreeMonoid.ofList w) =
      afterConsume p w (fun t => c * P (FreeMonoid.ofList t)) := by
  classical
  cases hc : consumePrefix p w with
  | none =>
    rw [afterConsume_of_none p w hc]
    apply MonoidAlgebra.single_mul_apply_of_not_exists_mul
    rintro ⟨m, hm⟩
    have hw : w = p ++ m.toList := by
      simpa only [FreeMonoid.toList_ofList, FreeMonoid.toList_mul] using
        congrArg FreeMonoid.toList hm
    exact consumePrefix_none_no_append p w hc ⟨m.toList, hw⟩
  | some t =>
    rw [afterConsume_of_some p w t hc]
    have hw : FreeMonoid.ofList w = FreeMonoid.ofList p * FreeMonoid.ofList t := by
      rw [(consumePrefix_eq_some_iff p w t).mp hc, FreeMonoid.ofList_append]
    apply MonoidAlgebra.single_mul_apply_aux
    intro m hm
    rw [hw]
    exact mul_left_cancel_iff

end CriticalGK2.Automaton
