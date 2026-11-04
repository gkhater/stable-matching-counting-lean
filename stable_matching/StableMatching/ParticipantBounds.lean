import StableMatching.StoppedCounting

/-! Participant-scaled query bounds for the actual reduction. -/

namespace StableMatching.StoppedCounting

open MathEconLib.Matching

theorem participant_height_budget (m n D : Nat) (hm : 0 < m) (hD : 0 < D) :
    1 + (8 * m * n : ℝ) / ((m * D : Nat) : ℝ) ≤ (2 + 8 * n / D : Nat) := by
  have hmod := Nat.mod_lt (8 * n) hD
  have hdivision := Nat.mod_add_div (8 * n) D
  have hnat : 8 * n < (8 * n / D + 1) * D := by nlinarith
  have hcast : (8 : ℝ) * n ≤ ((8 * n / D : Nat) + (1 : ℝ)) * D := by
    exact_mod_cast hnat.le
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hmul := mul_le_mul_of_nonneg_left hcast hm'.le
  have hden : (0 : ℝ) < ((m * D : Nat) : ℝ) := by positivity
  have hquot : (8 * m * n : ℝ) / ((m * D : Nat) : ℝ) ≤
      (8 * n / D : Nat) + (1 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    push_cast
    nlinarith
  push_cast at hquot ⊢
  linarith

theorem reduce_participant_query_bound {m n : Nat}
    (mkt : MarriageMarket (Fin m) (Fin n)) (D : Nat)
    (hm : 0 < m) (hn : 0 < n) (hD : 0 < D) :
    (reduce mkt (m * D)).length ≤ 2 ^ (2 + 8 * n / D) :=
  reduce_query_bound mkt (m * D) (2 + 8 * n / D)
    (Nat.mul_pos hm hD) (Nat.mul_pos hm hn)
    (participant_height_budget m n D hm hD)

end StableMatching.StoppedCounting
