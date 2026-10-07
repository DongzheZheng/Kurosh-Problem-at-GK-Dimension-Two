import CriticalGK2.NormalLanguageSurvival

/-!
# Normal-word lower bounds for an arbitrary actual word-algebra map

The map is a genuine algebra homomorphism from the original two-letter free
algebra into an arbitrary algebra. Survival of every actual homogeneous image and nilpotence of the images of
all nonempty words supply every-length normal words and exclude a periodic
tail. The factorial property, the stream, the factor count, and the greedy
pivot count are derived from the actual word images.
-/

namespace CriticalGK2.GenericLower

noncomputable section

open CriticalGK2.Actual CriticalGK2.WordOrder
open CriticalGK2.Language CriticalGK2.WordLanguage
open scoped BigOperators

variable (F : Type*) [Field F]
variable {B : Type*} [Ring B] [Algebra F B]
variable (φ : WordAlgebra F →ₐ[F] B)

/-- Actual singleton word images under the supplied homomorphism. -/
def wordImage (u : Word) : B := φ (MonoidAlgebra.single u 1)

theorem wordImage_mul (u v : Word) :
    wordImage F φ (u * v) = wordImage F φ u * wordImage F φ v := by
  unfold wordImage
  rw [← map_mul]
  congr 1
  simp only [MonoidAlgebra.single_mul_single, one_mul]

theorem wordImage_pow (u : Word) (m : ℕ) : wordImage F φ (u ^ m) = wordImage F φ u ^ m := by
  induction m with
  | zero => simp only [pow_zero, wordImage, ← MonoidAlgebra.one_def, map_one]
  | succ m ih => simp only [pow_succ, wordImage_mul, ih]

def earlierImages (u : Word) : Set B :=
  {z | ∃ v : Word, v.length = u.length ∧ wordNumber v < wordNumber u ∧ wordImage F φ v = z}

def Normal (u : Word) : Prop := wordImage F φ u ∉ Submodule.span F (earlierImages F φ u)

/-- Literal sandwich multiplication on the actual target algebra. -/
def imageSandwich (a b : Word) : B →ₗ[F] B where
  toFun z := wordImage F φ a * z * wordImage F φ b
  map_add' x y := by rw [mul_add, add_mul]
  map_smul' c x := by
    rw [mul_smul_comm, smul_mul_assoc]
    simp only [RingHom.id_apply]

@[simp]
theorem imageSandwich_word (a b v : Word) :
    imageSandwich F φ a b (wordImage F φ v) = wordImage F φ (a * v * b) := by
  change wordImage F φ a * wordImage F φ v * wordImage F φ b = _
  rw [wordImage_mul, wordImage_mul]

theorem earlierSpan_sandwich (a b u : Word) :
    Submodule.span F (earlierImages F φ u) ≤
      (Submodule.span F (earlierImages F φ (a * u * b))).comap (imageSandwich F φ a b) := by
  apply Submodule.span_le.mpr
  rintro z ⟨v, hlen, hcode, rfl⟩
  change imageSandwich F φ a b (wordImage F φ v) ∈
    Submodule.span F (earlierImages F φ (a * u * b))
  rw [imageSandwich_word]
  apply Submodule.subset_span
  refine ⟨a * v * b, ?_, wordNumber_sandwich_lt a b u v hlen hcode, rfl⟩
  simp only [FreeMonoid.length_mul, hlen]

/-- Factoriality is a consequence of actual multiplication, without any
assumption on the language or any all-cut presentation. -/
theorem normal_factor (a u b : Word) (h : Normal F φ (a * u * b)) : Normal F φ u := by
  classical
  by_contra hu
  have hmem : wordImage F φ u ∈ Submodule.span F (earlierImages F φ u) := by
    simpa only [Normal, not_not] using hu
  have hm := earlierSpan_sandwich F φ a b u hmem
  change imageSandwich F φ a b (wordImage F φ u) ∈
    Submodule.span F (earlierImages F φ (a * u * b)) at hm
  rw [imageSandwich_word] at hm
  exact h hm

theorem not_normal_of_image_zero (u : Word) (hu : wordImage F φ u = 0) : ¬ Normal F φ u := by
  intro h
  apply h
  rw [hu]
  exact Submodule.zero_mem _

/-- Actual degree-n map, with its true homogeneous source. -/
def homogeneousImageMap (n : ℕ) : homogeneous F n →ₗ[F] B :=
  φ.toLinearMap.comp (homogeneous F n).subtype

/-- The actual degree image in the original target algebra. -/
def degreeImage (n : ℕ) : Submodule F B := (homogeneous F n).map φ.toLinearMap

theorem homogeneousImageMap_range (n : ℕ) :
    LinearMap.range (homogeneousImageMap F φ n) = degreeImage F φ n := by
  apply Submodule.ext
  intro z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

instance degreeImage_finite (n : ℕ) : FiniteDimensional F (degreeImage F φ n) := by
  letI : FiniteDimensional F (homogeneous F n) :=
    (homogeneousWordBasis F n).finiteDimensional_of_finite
  rw [← homogeneousImageMap_range]
  exact Module.Finite.range (homogeneousImageMap F φ n)

@[simp]
theorem homogeneousImageMap_basis (n : ℕ) (w : LengthWord n) :
    homogeneousImageMap F φ n (homogeneousWordBasis F n w) = wordImage F φ w.val := by
  change φ ((homogeneousWordBasis F n w).val) = _
  rw [homogeneousWordBasis_coe]
  rfl

theorem wordImages_span_eq_degreeImage (n : ℕ) :
    Submodule.span F (Set.range (fun w : LengthWord n => wordImage F φ w.val)) = degreeImage F φ n := by
  classical
  rw [← homogeneousImageMap_range]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨w, rfl⟩
    exact ⟨homogeneousWordBasis F n w, homogeneousImageMap_basis F φ n w⟩
  · rintro z ⟨x, rfl⟩
    rw [← (homogeneousWordBasis F n).sum_repr x, map_sum]
    apply Submodule.sum_mem
    intro w _
    rw [map_smul, homogeneousImageMap_basis]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)

/-- The finite actual greedy word index, using the same explicit binary code. -/
def NormalIndex (n : ℕ) := Greedy.Index F
  (fun w : LengthWord n => wordImage F φ w.val) (fun w : LengthWord n => wordNumber w.val)

instance normalIndexFintype (n : ℕ) : Fintype (NormalIndex F φ n) := Greedy.indexFintype F _ _

theorem greedyEarlier_eq (n : ℕ) (w : LengthWord n) :
    Greedy.Earlier (fun v : LengthWord n => wordImage F φ v.val)
      (fun v : LengthWord n => wordNumber v.val) w = earlierImages F φ w.val := by
  ext z
  constructor
  · rintro ⟨v, hcode, hz⟩
    exact ⟨v.val, v.property.trans w.property.symm, hcode, hz⟩
  · rintro ⟨v, hlen, hcode, hz⟩
    exact ⟨⟨v, hlen.trans w.property⟩, hcode, hz⟩

theorem normalIndex_normal (n : ℕ) (w : NormalIndex F φ n) : Normal F φ w.val.val := by
  have hw := w.property
  change wordImage F φ w.val.val ∉ Submodule.span F
    (Greedy.Earlier (fun v : LengthWord n => wordImage F φ v.val)
      (fun v : LengthWord n => wordNumber v.val) w.val) at hw
  rw [greedyEarlier_eq] at hw
  exact hw

/-- Actual pivot count equals the dimension of the true degree image. -/
theorem card_normalIndex_eq_finrank_degreeImage (n : ℕ) :
    Fintype.card (NormalIndex F φ n) = Module.finrank F (degreeImage F φ n) := by
  have h := Greedy.card_index_eq_finrank_span F
    (fun w : LengthWord n => wordImage F φ w.val)
    (fun w : LengthWord n => wordNumber w.val) (lengthWordNumber_injective n)
  rw [wordImages_span_eq_degreeImage] at h
  exact h

/-- Every surviving actual homogeneous image supplies an actual normal word. -/
theorem exists_normal_of_degreeImage_ne_bot (n : ℕ) (hn : degreeImage F φ n ≠ ⊥) :
    ∃ w : LengthWord n, Normal F φ w.val := by
  classical
  have hnIndex : Nonempty (NormalIndex F φ n) := by
    by_contra h
    letI : IsEmpty (NormalIndex F φ n) := ⟨fun w => h ⟨w⟩⟩
    have he : Submodule.span F (Set.range (Greedy.family F
      (fun w : LengthWord n => wordImage F φ w.val)
      (fun w : LengthWord n => wordNumber w.val))) = ⊥ := by
      apply eq_bot_iff.mpr
      apply Submodule.span_le.mpr
      rintro z ⟨w, rfl⟩
      exact False.elim (h ⟨w⟩)
    apply hn
    rw [← wordImages_span_eq_degreeImage, ← Greedy.span_family_eq_span F
      (fun w : LengthWord n => wordImage F φ w.val)
      (fun w : LengthWord n => wordNumber w.val), he]
  obtain ⟨w⟩ := hnIndex
  exact ⟨w.val, normalIndex_normal F φ n w⟩

def normalLanguage : Set (List Bool) := {u | Normal F φ (FreeMonoid.ofList u)}

theorem normalLanguage_factorClosed : FactorClosed (normalLanguage F φ) := by
  intro u v huv hv
  obtain ⟨a, b, rfl⟩ := huv
  apply normal_factor F φ (FreeMonoid.ofList a) (FreeMonoid.ofList u) (FreeMonoid.ofList b)
  simpa only [normalLanguage, Set.mem_setOf_eq, FreeMonoid.ofList_append] using hv

theorem normalLanguage_every_length (hsurvive : ∀ n : ℕ, degreeImage F φ n ≠ ⊥) :
    ∀ n : ℕ, ∃ u : List Bool, u ∈ normalLanguage F φ ∧ u.length = n := by
  intro n
  obtain ⟨w, hw⟩ := exists_normal_of_degreeImage_ne_bot F φ n (hsurvive n)
  refine ⟨w.val.toList, ?_, w.property⟩
  change Normal F φ (FreeMonoid.ofList w.val.toList)
  rw [FreeMonoid.ofList_toList]
  exact hw

/-- Nilness of nonempty word images excludes a periodic tail of a genuine
stream whose actual factors are normal. -/
theorem normal_stream_not_tailPeriodic
    (hnil : ∀ u : Word, u ≠ 1 → ∃ m : ℕ, 0 < m ∧ wordImage F φ u ^ m = 0)
    (x : ℕ → Bool) (hx : ∀ s n : ℕ, streamFactor x s n ∈ normalLanguage F φ) :
    ¬ TailPeriodic x := by
  rintro ⟨s, p, hp, hperiod⟩
  let u : Word := FreeMonoid.ofList (streamFactor x s p)
  have hu : u ≠ 1 := by
    intro he
    have hlen := congrArg FreeMonoid.length he
    change (streamFactor x s p).length = 0 at hlen
    rw [streamFactor_length] at hlen
    omega
  obtain ⟨m, _, hm⟩ := hnil u hu
  have hnot := not_normal_of_image_zero F φ (u ^ m) (by rw [wordImage_pow]; exact hm)
  apply hnot
  have hnormal : Normal F φ (FreeMonoid.ofList (streamFactor x s (m * p))) := hx s (m * p)
  rw [periodic_streamFactor_word_power x s p hperiod m] at hnormal
  exact hnormal

/-- Recording the complete literal factor gives a true finite greedy index. -/
def factorToNormalIndex (x : ℕ → Bool)
    (hx : ∀ s n : ℕ, streamFactor x s n ∈ normalLanguage F φ) (n : ℕ) :
    Factor x n → NormalIndex F φ n := fun f =>
  ⟨lengthWordOfFactor x n f, by
    change wordImage F φ (lengthWordOfFactor x n f).val ∉ Submodule.span F
      (Greedy.Earlier (fun v : LengthWord n => wordImage F φ v.val)
        (fun v : LengthWord n => wordNumber v.val) (lengthWordOfFactor x n f))
    rw [greedyEarlier_eq]
    obtain ⟨i, hi⟩ := f.property
    change Normal F φ (FreeMonoid.ofList (List.ofFn f.val))
    rw [← hi]
    exact hx i n⟩

theorem factorToNormalIndex_injective (x : ℕ → Bool)
    (hx : ∀ s n : ℕ, streamFactor x s n ∈ normalLanguage F φ) (n : ℕ) :
    Function.Injective (factorToNormalIndex F φ x hx n) := by
  intro f g hfg
  have hword : FreeMonoid.ofList (List.ofFn f.val) = FreeMonoid.ofList (List.ofFn g.val) :=
    congrArg (fun w : NormalIndex F φ n => w.val.val) hfg
  have hlist : List.ofFn f.val = List.ofFn g.val := congrArg FreeMonoid.toList hword
  exact Subtype.ext (List.ofFn_injective hlist)

theorem factorComplexity_le_degreeImage_finrank (x : ℕ → Bool)
    (hx : ∀ s n : ℕ, streamFactor x s n ∈ normalLanguage F φ) (n : ℕ) :
    factorComplexity x n ≤ Module.finrank F (degreeImage F φ n) := by
  have hcard := Fintype.card_le_of_injective (factorToNormalIndex F φ x hx n)
    (factorToNormalIndex_injective F φ x hx n)
  rw [card_normalIndex_eq_finrank_degreeImage] at hcard
  exact hcard

/-- The generic algebraic lower bound: all language, path, factor-count,
and basis conditions have been constructed from the two ordinary inputs. -/
theorem degreeImage_finrank_lower
    (hsurvive : ∀ n : ℕ, degreeImage F φ n ≠ ⊥)
    (hnil : ∀ u : Word, u ≠ 1 → ∃ m : ℕ, 0 < m ∧ wordImage F φ u ^ m = 0)
    (n : ℕ) : n + 1 ≤ Module.finrank F (degreeImage F φ n) := by
  obtain ⟨x, hx⟩ := exists_stream_factors_mem (normalLanguage F φ)
    (normalLanguage_factorClosed F φ) (normalLanguage_every_length F φ hsurvive)
  have hlower := factorComplexity_ge_length_add_one_of_not_tailPeriodic x
    (normal_stream_not_tailPeriodic F φ hnil x hx) n
  exact hlower.trans (factorComplexity_le_degreeImage_finrank F φ x hx n)

#print axioms CriticalGK2.GenericLower.normal_factor
#print axioms CriticalGK2.GenericLower.card_normalIndex_eq_finrank_degreeImage
#print axioms CriticalGK2.GenericLower.degreeImage_finrank_lower

end

end CriticalGK2.GenericLower
