import StableMatching.CompactReduction
import StableMatching.CompactRates
import Wrap.ArithRate

/-! An explicit parameter-dependent exponent for the actual compact queries.
The width is allowed to vary here; no fixed-width constant hides its cost. -/

namespace StableMatching.RateTradeoff

open MathEconLib.Matching

noncomputable def queryExponent (C n ℓ : Nat) : ℝ :=
  (C : ℝ) * (max (2 * ℓ) 2 : Nat) ^ 2 *
    (((2 * n * ℓ : Nat) : ℝ) + 4) * SatK.rN 1 (1 / 2) (2 * n * ℓ)

noncomputable def exponent (C n D ℓ : Nat) : ℝ :=
  ((2 + 8 * n / D : Nat) : ℝ) + queryExponent C n ℓ

theorem prepared_query_bound (C n ℓ : Nat) (φ : CNF)
    (hvars : φ.numVars ≤ 2 * n * ℓ) :
    (MainResults.timeMin C (max (2 * ℓ) 2)
      φ.prepare.clauses.length φ.prepare.numVars : ℝ) ≤
        (2 : ℝ) ^ queryExponent C n ℓ := by
  have hN : φ.prepare.numVars ≤ 2 * n * ℓ + 4 := by
    simpa only [CNF.prepare_numVars] using Nat.add_le_add_right hvars 4
  have hrate := Wrap.Arith.exponent_le (n := 2 * n * ℓ)
    (n' := φ.prepare.numVars) (by simp) hN
  have hscaled := mul_le_mul_of_nonneg_left hrate
    (show 0 ≤ (C : ℝ) * (max (2 * ℓ) 2 : Nat) ^ 2 by positivity)
  apply (CompactRates.timeMin_le_rate C (max (2 * ℓ) 2)
    φ.prepare.clauses.length φ.prepare.numVars).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  simpa only [queryExponent, mul_assoc] using hscaled

private theorem sum_le_length_mul {α : Type*} (xs : List α) (f : α → ℝ) (K : ℝ)
    (h : ∀ x ∈ xs, f x ≤ K) : (xs.map f).sum ≤ xs.length * K := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem compact_query_budget {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (C D : Nat) (hD : 0 < D) (ℓ : Nat) (hn : 0 < n) :
    ((CompactReduction.reduce mkt D hD ℓ).map (fun φ =>
      (MainResults.timeMin C (max (2 * ℓ) 2)
        φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
          (2 : ℝ) ^ exponent C n D ℓ := by
  have hlen : ((CompactReduction.reduce mkt D hD ℓ).length : ℝ) ≤
      (2 : ℝ) ^ ((2 + 8 * n / D : Nat) : ℝ) := by
    exact_mod_cast CompactReduction.reduce_query_bound mkt D hD ℓ hn hn
  calc
    ((CompactReduction.reduce mkt D hD ℓ).map (fun φ =>
      (MainResults.timeMin C (max (2 * ℓ) 2)
        φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
        (CompactReduction.reduce mkt D hD ℓ).length *
          (2 : ℝ) ^ queryExponent C n ℓ := by
      apply sum_le_length_mul
      intro φ hφ
      exact prepared_query_bound C n ℓ φ
        (CompactReduction.reduce_variable_bound mkt D hD ℓ φ hφ)
    _ ≤ (2 : ℝ) ^ ((2 + 8 * n / D : Nat) : ℝ) *
        (2 : ℝ) ^ queryExponent C n ℓ :=
      mul_le_mul_of_nonneg_right hlen (by positivity)
    _ = (2 : ℝ) ^ exponent C n D ℓ := by
      rw [← Real.rpow_add (by norm_num)]
      rfl

end StableMatching.RateTradeoff
