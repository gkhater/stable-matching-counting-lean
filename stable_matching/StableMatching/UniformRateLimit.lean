import StableMatching.LogarithmicRate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The fourth-root-logarithmic matching-query exponent is below every fixed
positive linear exponent, with a finite multiplicative constant. -/

namespace StableMatching.UniformRateLimit

open Filter

theorem rootScale_tendsto_atTop :
    Tendsto LogarithmicRate.rootScale atTop atTop := by
  have hnat : Tendsto (fun n : Nat => (n : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  have hlog : Tendsto LogarithmicRate.logScale atTop atTop := by
    exact (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hnat
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hlog

/-- A concrete fourth-root-log rate can be absorbed into any positive
participant exponent. The natural constant covers the finite initial segment. -/
theorem exponent_below {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ b : Nat, ∀ n : Nat, 1 ≤ n →
      (2 : ℝ) ^ (A * (n : ℝ) / LogarithmicRate.rootScale n) ≤
        (b : ℝ) * (2 : ℝ) ^ (ε * (n : ℝ)) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((tendsto_atTop.1 rootScale_tendsto_atTop) (A / ε))
  obtain ⟨b, hb⟩ := exists_nat_gt ((2 : ℝ) ^ (A * (N : ℝ)))
  refine ⟨b, ?_⟩
  intro n hn
  have hroot := LogarithmicRate.rootScale_ge_one n
  have hrootpos : 0 < LogarithmicRate.rootScale n := by linarith
  have hbpos : (1 : ℝ) ≤ b := by
    have hpow : 0 < (2 : ℝ) ^ (A * (N : ℝ)) := by positivity
    have hb0 : (0 : ℝ) < (b : ℝ) := lt_trans hpow hb
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (by exact_mod_cast hb0)))
  by_cases hlarge : N ≤ n
  · have hscale : A / ε ≤ LogarithmicRate.rootScale n := hN n hlarge
    have hAroot : A ≤ ε * LogarithmicRate.rootScale n := by
      exact (div_le_iff₀ hε).mp hscale |>.trans_eq (mul_comm _ _)
    have hexp : A * (n : ℝ) / LogarithmicRate.rootScale n ≤
        ε * (n : ℝ) := by
      apply (div_le_iff₀ hrootpos).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hAroot) (Nat.cast_nonneg n)]
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hsecond : (2 : ℝ) ^ (ε * (n : ℝ)) ≤
        (b : ℝ) * (2 : ℝ) ^ (ε * (n : ℝ)) := by
      nlinarith [show 0 ≤ (2 : ℝ) ^ (ε * (n : ℝ)) by positivity]
    exact hp.trans hsecond
  · have hnN : (n : ℝ) ≤ N := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hlarge))
    have hsmall : A * (n : ℝ) / LogarithmicRate.rootScale n ≤ A * (N : ℝ) := by
      apply (div_le_iff₀ hrootpos).mpr
      have hAN : A * (n : ℝ) ≤ A * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hnN hA
      have hnonneg : 0 ≤ A * (N : ℝ) := by positivity
      nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hroot)]
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hsmall
    have hone : 1 ≤ (2 : ℝ) ^ (ε * (n : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hε.le (Nat.cast_nonneg n))
    have hsecond : (2 : ℝ) ^ (A * (N : ℝ)) ≤
        (b : ℝ) * (2 : ℝ) ^ (ε * (n : ℝ)) := by
      have hbR : (2 : ℝ) ^ (A * (N : ℝ)) ≤ (b : ℝ) := hb.le
      nlinarith
    exact hp.trans hsecond

end StableMatching.UniformRateLimit
