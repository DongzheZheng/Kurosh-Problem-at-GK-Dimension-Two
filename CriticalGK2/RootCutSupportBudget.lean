import CriticalGK2.RootContractionTensorBridge
import CriticalGK2.FreeTailCutSupport

/-!
# Raw root completions and actual full tensor cut supports

These identities apply to any raw dyadic dual family. They identify the
previously proved completion-annihilator spaces with the honest tensor
support operations used in the computed stem budget. The maps are the actual
inverse degree transports and inverse homogeneous dual concatenations.
-/

namespace CriticalGK2.Actual

noncomputable section

open TensorProduct CriticalGK2.ContractionBudget

variable (F : Type*) [Field F]

def actualRootPrefixTensorCutMap (n : ℕ) :
    HomogeneousDual F (2 ^ strictDyadicRoot n) →ₗ[F]
      HomogeneousDual F n ⊗[F] HomogeneousDual F (2 ^ strictDyadicRoot n - n) :=
  (homogeneousDualTensorConcat F n (2 ^ strictDyadicRoot n - n)).symm.toLinearMap.comp
    (homogeneousDualDegreeCast F (completionRootDegree n)).symm.toLinearMap

def actualRootSuffixTensorCutMap (n : ℕ) :
    HomogeneousDual F (2 ^ strictDyadicRoot n) →ₗ[F]
      HomogeneousDual F (2 ^ strictDyadicRoot n - n) ⊗[F] HomogeneousDual F n :=
  (homogeneousDualTensorConcat F (2 ^ strictDyadicRoot n - n) n).symm.toLinearMap.comp
    (homogeneousDualDegreeCast F (completionRootDegreeLeft n)).symm.toLinearMap

theorem actualRootPrefixContractionSupport_eq_tensorPrefixSupport
    (W : DyadicDualData F) (n : ℕ) :
    actualRootPrefixContractionSupport F W n =
      tensorPrefixSupport ((W (strictDyadicRoot n)).map (actualRootPrefixTensorCutMap F n)) := by
  unfold actualRootPrefixContractionSupport tensorPrefixSupport
  apply iSup_congr
  intro eta
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro phi
  change actualRootPrefixContraction F n eta phi =
    contractRight eta ((homogeneousDualTensorConcat F n (2 ^ strictDyadicRoot n - n)).symm
      ((homogeneousDualDegreeCast F (completionRootDegree n)).symm phi))
  exact actualRootPrefixContraction_eq_contractRight F n eta phi

theorem actualRootSuffixContractionSupport_eq_tensorSuffixSupport
    (W : DyadicDualData F) (n : ℕ) :
    actualRootSuffixContractionSupport F W n =
      tensorSuffixSupport ((W (strictDyadicRoot n)).map (actualRootSuffixTensorCutMap F n)) := by
  unfold actualRootSuffixContractionSupport tensorSuffixSupport
  apply iSup_congr
  intro eta
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro phi
  change actualRootSuffixContraction F n eta phi =
    extendedPair eta ((homogeneousDualTensorConcat F (2 ^ strictDyadicRoot n - n) n).symm
      ((homogeneousDualDegreeCast F (completionRootDegreeLeft n)).symm phi))
  exact actualRootSuffixContraction_eq_extendedPair F n eta phi

theorem homogeneousRightCompletion_dualAnnihilator_finrank_eq_tensorPrefixSupport
    (W : DyadicDualData F) (n : ℕ) (hn : n ≠ 0) :
    Module.finrank F ((homogeneousRightCompletion F W n).dualAnnihilator) =
      Module.finrank F (tensorPrefixSupport
        ((W (strictDyadicRoot n)).map (actualRootPrefixTensorCutMap F n))) := by
  rw [homogeneousRightCompletion_dualAnnihilator F W n hn,
    actualRootPrefixContractionSupport_eq_tensorPrefixSupport]

theorem homogeneousLeftCompletion_dualAnnihilator_finrank_eq_tensorSuffixSupport
    (W : DyadicDualData F) (n : ℕ) (hn : n ≠ 0) :
    Module.finrank F ((homogeneousLeftCompletion F W n).dualAnnihilator) =
      Module.finrank F (tensorSuffixSupport
        ((W (strictDyadicRoot n)).map (actualRootSuffixTensorCutMap F n))) := by
  rw [homogeneousLeftCompletion_dualAnnihilator F W n hn,
    actualRootSuffixContractionSupport_eq_tensorSuffixSupport]

#print axioms CriticalGK2.Actual.actualRootPrefixContractionSupport_eq_tensorPrefixSupport

end

end CriticalGK2.Actual
