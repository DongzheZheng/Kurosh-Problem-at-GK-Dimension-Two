import CriticalGK2.GrowthExponent
import CriticalGK2.SparseBudgetIndex

/-!
# Scheduled support budgets imply every upper exponent above two

The support budget and its paid-operation count are the actual quantities
computed by the sparse schedule. The schedule proves C_j^j <= n and proves
that every fixed operation count J is eventually paid. Raising C_j^J <= n
to a positive real exponent epsilon, with J*epsilon >= 2, gives C_j^2 <=
n^epsilon. The remaining finite initial segment is absorbed into one literal
positive multiplicative constant.

Only the numerical upper bound on the actual growth function is an input
here. The index bound and eventual operation count give the estimates
for every polynomial exponent above two.
-/

namespace CriticalGK2.Growth

open CriticalGK2.Actual

noncomputable section

/-- The elementary exponent comparison underlying the schedule argument. -/
theorem budget_square_le_rpow_of_power_bound
    (c j J n : ℕ) (ε : ℝ) (hc : 0 < c) (hJ : J ≤ j)
    (hpower : c ^ j ≤ n) (hε : 0 ≤ ε)
    (hexponent : (2 : ℝ) ≤ (J : ℝ) * ε) :
    (c : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) ^ ε := by
  have hpowJ : c ^ J ≤ n :=
    (Nat.pow_le_pow_right hc hJ).trans hpower
  have hcOne : (1 : ℝ) ≤ (c : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hc)
  have hcNonneg : (0 : ℝ) ≤ (c : ℝ) := by positivity
  have hrealPower : (c : ℝ) ^ (J : ℝ) ≤ (n : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hpowJ
  calc
    (c : ℝ) ^ (2 : ℕ) = (c : ℝ) ^ (2 : ℝ) := (Real.rpow_two _).symm
    _ ≤ (c : ℝ) ^ ((J : ℝ) * ε) :=
      Real.rpow_le_rpow_of_exponent_le hcOne hexponent
    _ = ((c : ℝ) ^ (J : ℝ)) ^ ε := Real.rpow_mul hcNonneg _ _
    _ ≤ (n : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hrealPower hε

/-- A literal global n(n+1)C_j(n)^2 bound yields every polynomial upper
exponent 2+epsilon for the same growth function and the same schedule. -/
theorem near_two_upper_of_scheduled_budget (Λ : ℕ → ℝ)
    (hΛ : EnvelopeDiverges Λ) (γ : ℕ → ℕ) (hγ : Monotone γ)
    (hbound : ∀ n : ℕ, 0 < n →
      γ n ≤ n * (n + 1) *
        supportBudget targetCost
          (begunOperationCount Λ hΛ (strictDyadicRoot n)) ^ 2)
    (ε : ℝ) (hε : 0 < ε) : 2 + ε ∈ UpperExponentSet γ := by
  obtain ⟨J, hJlarge⟩ := exists_nat_gt ((2 : ℝ) / ε)
  have hJposReal : (0 : ℝ) < (J : ℝ) :=
    (div_pos (by norm_num) hε).trans hJlarge
  have hJpos : 0 < J := by exact_mod_cast hJposReal
  have hJeps : (2 : ℝ) ≤ (J : ℝ) * ε :=
    le_of_lt ((div_lt_iff₀ hε).mp hJlarge)
  let N₀ : ℕ := 2 ^ scheduledHeight Λ hΛ (J - 1)
  let C : ℝ := 2 + (γ N₀ : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposNat
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpowNonneg : 0 ≤ (n : ℝ) ^ (2 + ε) :=
    le_of_lt (Real.rpow_pos_of_pos hnpos _)
  by_cases hlarge : N₀ ≤ n
  · let j : ℕ := begunOperationCount Λ hΛ (strictDyadicRoot n)
    let c : ℕ := supportBudget targetCost j
    have hj : J ≤ j :=
      root_operation_count_ge_after_threshold Λ hΛ J n hJpos hlarge
    have hpower : c ^ j ≤ n :=
      root_operation_budget_power_le_degree Λ hΛ n hnposNat
    have hc : 0 < c := supportBudget_pos targetCost j
    have hsquare : (c : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) ^ ε :=
      budget_square_le_rpow_of_power_bound c j J n ε hc hj hpower
        (le_of_lt hε) hJeps
    have hg : (γ n : ℝ) ≤
        (n : ℝ) * ((n : ℝ) + 1) * (c : ℝ) ^ (2 : ℕ) := by
      exact_mod_cast hbound n hnposNat
    have hnplus : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    have htwo : (γ n : ℝ) ≤ 2 * (n : ℝ) ^ (2 + ε) := by
      calc
        (γ n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) * (c : ℝ) ^ (2 : ℕ) := hg
        _ ≤ (n : ℝ) * ((n : ℝ) + 1) * (n : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left hsquare (by positivity)
        _ ≤ (n : ℝ) * (2 * (n : ℝ)) * (n : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnplus (le_of_lt hnpos)) (by positivity)
        _ = 2 * (n : ℝ) ^ (2 + ε) := by
          rw [Real.rpow_add hnpos, Real.rpow_two]
          ring
    have hCtwo : (2 : ℝ) ≤ C := by
      dsimp only [C]
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    exact htwo.trans (mul_le_mul_of_nonneg_right hCtwo hnpowNonneg)
  · have hnsmall : n ≤ N₀ := by omega
    have hg : (γ n : ℝ) ≤ (γ N₀ : ℝ) := by exact_mod_cast hγ hnsmall
    have hpowOne : (1 : ℝ) ≤ (n : ℝ) ^ (2 + ε) :=
      Real.one_le_rpow hnOne (by linarith)
    calc
      (γ n : ℝ) ≤ (γ N₀ : ℝ) := hg
      _ ≤ C := by dsimp [C]; linarith
      _ ≤ C * (n : ℝ) ^ (2 + ε) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hpowOne (le_of_lt hC)

#print axioms CriticalGK2.Growth.budget_square_le_rpow_of_power_bound
#print axioms CriticalGK2.Growth.near_two_upper_of_scheduled_budget

end

end CriticalGK2.Growth
