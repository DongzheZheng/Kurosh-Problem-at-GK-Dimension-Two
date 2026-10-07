import CriticalGK2.InfiniteSpaces
import CriticalGK2.DualFamilyBridge
import CriticalGK2.BlockPropagation
import CriticalGK2.GradedSurvival
import CriticalGK2.DualStageSteps

/-!
# Concrete objects from the infinite polynomial construction

The construction supplies the dual data, primal coherence, ideal and
positive non-unital quotient. All-cut readback converts the PI endpoint
kernels into nilpotence relations in the quotient.
-/

namespace CriticalGK2.Actual

noncomputable section

variable (F : Type*) [Field F] (waiting size : ℕ → ℕ)

def constructedDualData : DyadicDualData F :=
  actualDualFamily F (infiniteSpace F waiting size)

theorem constructedDualData_coherent : DualCoherent F (constructedDualData F waiting size) :=
  actualDualFamily_dualCoherent F (infiniteSpace F waiting size)
    (infiniteSpace_le_homogeneous F waiting size) (infiniteSpace_coherent F waiting size)

theorem constructedPrimalCoherent : PrimalCoherent F (constructedDualData F waiting size) :=
  dualCoherent_primalCoherent F _ (constructedDualData_coherent F waiting size)

theorem constructedDualData_ne_bot (h : ℕ) :
    constructedDualData F waiting size h ≠ ⊥ :=
  actualDualFamily_ne_bot F (infiniteSpace F waiting size)
    (infiniteSpace_le_homogeneous F waiting size) (infiniteSpace_ne_bot F waiting size) h

/-- The actual positive non-unital all-cut quotient. -/
def ConstructedPositiveAlgebra : Type _ :=
  PositiveAllCutQuotient F (constructedDualData F waiting size)
    (constructedPrimalCoherent F waiting size)

/-- Every positive homogeneous quotient survives in this concrete construction. -/
theorem constructed_component_nontrivial (n : ℕ) (hn : n ≠ 0) :
    Nontrivial (ComponentQuotient F (constructedDualData F waiting size) n) :=
  componentQuotient_nontrivial F _ n hn
    (constructedDualData_ne_bot F waiting size (strictDyadicRoot n))

theorem constructed_positive_nontrivial :
    Nontrivial (ConstructedPositiveAlgebra F waiting size) :=
  positiveAllCutQuotient_nontrivial F _ (constructedPrimalCoherent F waiting size)
    1 (by decide) (constructedDualData_ne_bot F waiting size (strictDyadicRoot 1))

theorem constructed_positive_not_finite :
    ¬ Module.Finite F (PositiveAllCutQuotient F (constructedDualData F waiting size)
      (constructedPrimalCoherent F waiting size)) :=
  positiveAllCutQuotient_not_finite F _ (constructedPrimalCoherent F waiting size)
    (constructedDualData_ne_bot F waiting size)

/-- Future dyadic layers contain actual whole blocks of every completed PI
stage, before any external contraction is taken. -/
theorem constructed_future_whole_blocks (j a : ℕ) :
    infiniteSpace F waiting size (stageHeight F waiting size (j + 1) + a) ≤
      blockPower F (infiniteSpace F waiting size (stageHeight F waiting size (j + 1)))
        (2 ^ a) :=
  coherent_family_le_blockPower F (infiniteSpace F waiting size)
    (infiniteSpace_coherent F waiting size) _ _

/-- Actual dual PI endpoint kernels, with arbitrary commutative coefficient
algebra and actual letter matrices. -/
theorem constructed_dual_endpoint_killed (C : Type*) [CommRing C] [Algebra F C]
    (j : ℕ) (v : Bool → Matrix (Fin (size j)) (Fin (size j)) C) :
    constructedDualData F waiting size (stageHeight F waiting size (j + 1)) ≤
      LinearMap.ker (actualDualMatrixEvaluation F C (size j)
        (2 ^ stageHeight F waiting size (j + 1)) v) := by
  change dualCoefficientSpace F (2 ^ stageHeight F waiting size (j + 1))
    (infiniteSpace F waiting size (stageHeight F waiting size (j + 1))) ≤ _
  exact dualCoefficientSpace_le_matrix_kernel F C (size j) _ v _
    (infiniteSpace_le_homogeneous F waiting size _)
    (infiniteSpace_stage_endpoint_killed F waiting size C j
      (binaryEvaluation F (Matrix (Fin (size j)) (Fin (size j)) C) v))

#print axioms CriticalGK2.Actual.constructedDualData_coherent
#print axioms CriticalGK2.Actual.constructedPrimalCoherent
#print axioms CriticalGK2.Actual.constructedDualData_ne_bot
#print axioms CriticalGK2.Actual.constructed_component_nontrivial
#print axioms CriticalGK2.Actual.constructed_dual_endpoint_killed

end

end CriticalGK2.Actual
