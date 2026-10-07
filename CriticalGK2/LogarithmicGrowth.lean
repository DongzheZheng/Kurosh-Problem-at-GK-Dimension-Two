import CriticalGK2.GrowthExponent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.Field

/-!
# The manuscript's logarithmic definition of growth dimension

Quadratic lower growth and polynomial upper growth at every exponent above
two imply convergence of the actual logarithmic ratio. Consequently its
limsup equals two as well. This supplies the definition used in the paper
directly, including positivity before taking logarithms or dividing.
-/

namespace CriticalGK2.Growth

open Filter
open scoped Topology

noncomputable section

def logarithmicGrowthRatio (γ : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.log (γ n : ℝ) / Real.log (n : ℝ)

theorem logarithmic_ratio_lower (γ : ℕ → ℕ)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (2 : ℕ) ≤ 2 * (γ n : ℝ))
    (n : ℕ) (hn : 2 ≤ n) :
    2 - Real.log 2 / Real.log (n : ℝ) ≤ logarithmicGrowthRatio γ n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hl := hlower n (by omega)
  have hgpos : (0 : ℝ) < (γ n : ℝ) := by nlinarith
  have hlogbound := (Real.log_le_log_iff (pow_pos hnpos 2)
    (mul_pos (by norm_num : (0 : ℝ) < 2) hgpos)).mpr hl
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hgpos)] at hlogbound
  change 2 - Real.log 2 / Real.log (n : ℝ) ≤ Real.log (γ n : ℝ) / Real.log (n : ℝ)
  calc
    2 - Real.log 2 / Real.log (n : ℝ) =
        (2 * Real.log (n : ℝ) - Real.log 2) / Real.log (n : ℝ) := by
      field_simp [ne_of_gt hlog]
    _ ≤ Real.log (γ n : ℝ) / Real.log (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num at hlogbound; linarith) (le_of_lt hlog)

theorem logarithmic_ratio_upper (γ : ℕ → ℕ)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (2 : ℕ) ≤ 2 * (γ n : ℝ))
    (d C : ℝ) (hC : 0 < C)
    (hupper : ∀ n : ℕ, 1 ≤ n → (γ n : ℝ) ≤ C * (n : ℝ) ^ d)
    (n : ℕ) (hn : 2 ≤ n) :
    logarithmicGrowthRatio γ n ≤ d + Real.log C / Real.log (n : ℝ) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hl := hlower n (by omega)
  have hgpos : (0 : ℝ) < (γ n : ℝ) := by nlinarith
  have hlogbound := (Real.log_le_log_iff hgpos
    (mul_pos hC (Real.rpow_pos_of_pos hnpos d))).mpr (hupper n (by omega))
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos hnpos d)),
    Real.log_rpow hnpos] at hlogbound
  change Real.log (γ n : ℝ) / Real.log (n : ℝ) ≤ d + Real.log C / Real.log (n : ℝ)
  calc
    Real.log (γ n : ℝ) / Real.log (n : ℝ) ≤
        (Real.log C + d * Real.log (n : ℝ)) / Real.log (n : ℝ) :=
      div_le_div_of_nonneg_right hlogbound (le_of_lt hlog)
    _ = d + Real.log C / Real.log (n : ℝ) := by field_simp [ne_of_gt hlog]; ring

theorem tendsto_logarithmicGrowthRatio_two (γ : ℕ → ℕ)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (2 : ℕ) ≤ 2 * (γ n : ℝ))
    (hupper : ∀ ε : ℝ, 0 < ε → 2 + ε ∈ UpperExponentSet γ) :
    Tendsto (logarithmicGrowthRatio γ) atTop (𝓝 2) := by
  have hlogtop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have ht : Tendsto (fun n : ℕ => Real.log 2 / Real.log (n : ℝ)) atTop (𝓝 0) :=
      hlogtop.const_div_atTop (Real.log 2)
    have he : ∀ᶠ n : ℕ in atTop, Real.log 2 / Real.log (n : ℝ) < 2 - a :=
      ht.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < 2 - a))
    filter_upwards [he, eventually_ge_atTop 2] with n hn hn2
    have hb := logarithmic_ratio_lower γ hlower n hn2
    linarith
  · intro a ha
    let ε : ℝ := (a - 2) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨C, hC, hu⟩ := hupper ε hε
    have ht : Tendsto (fun n : ℕ => Real.log C / Real.log (n : ℝ)) atTop (𝓝 0) :=
      hlogtop.const_div_atTop (Real.log C)
    have he : ∀ᶠ n : ℕ in atTop, Real.log C / Real.log (n : ℝ) < ε :=
      ht.eventually (eventually_lt_nhds hε)
    filter_upwards [he, eventually_ge_atTop 2] with n hn hn2
    have hb := logarithmic_ratio_upper γ hlower (2 + ε) C hC hu n hn2
    dsimp only [ε] at hn hb
    linarith

theorem limsup_logarithmicGrowthRatio_two (γ : ℕ → ℕ)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (2 : ℕ) ≤ 2 * (γ n : ℝ))
    (hupper : ∀ ε : ℝ, 0 < ε → 2 + ε ∈ UpperExponentSet γ) :
    Filter.limsup (logarithmicGrowthRatio γ) atTop = 2 :=
  (tendsto_logarithmicGrowthRatio_two γ hlower hupper).limsup_eq

#print axioms CriticalGK2.Growth.tendsto_logarithmicGrowthRatio_two
#print axioms CriticalGK2.Growth.limsup_logarithmicGrowthRatio_two

end

end CriticalGK2.Growth
