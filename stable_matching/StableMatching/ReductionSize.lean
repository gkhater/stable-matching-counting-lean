import StableMatching.PreparationSize
import StableMatching.CountingRates

/-! The total materialized normalized formula size is subexponential in the
number of participants. This is an output-size statement, not a compiler
running-time assertion. -/

namespace StableMatching.ReductionSize

open MathEconLib.Matching

def sizeConstant (D : Nat) : Nat :=
  let ℓ := CompactSize.bitWidth D
  let A := D * (2 * (D + 1))
  (A + A * A + 2 * ℓ + 8) * max (2 * ℓ) 2

private theorem quadratic_envelope (m A ℓ : Nat) :
    m * A + (m * A) * (m * A) + 2 * m * ℓ + 8 ≤
      (A + A * A + 2 * ℓ + 8) * (m + 2) ^ 2 := by
  have hm : m ≤ (m + 2) ^ 2 := by nlinarith
  have hm2 : m * m ≤ (m + 2) ^ 2 := by nlinarith
  have h1 : 1 ≤ (m + 2) ^ 2 := by nlinarith
  have hA := Nat.mul_le_mul_left A hm
  have hA2 := Nat.mul_le_mul_left (A * A) hm2
  have hL := Nat.mul_le_mul_left (2 * ℓ) hm
  have h8 := Nat.mul_le_mul_left 8 h1
  nlinarith

theorem prepared_literal_bound {m n : Nat} (mkt : MarriageMarket (Fin m) (Fin n))
    (D : Nat) (hD : 0 < D) :
    ∀ φ ∈ CompactReduction.reduce mkt D hD (CompactSize.bitWidth D),
      φ.prepare.literalCount ≤ sizeConstant D * (m + 2) ^ 2 := by
  intro φ hφ
  let ℓ := CompactSize.bitWidth D
  let A := D * (2 * (D + 1))
  have hc := φ.prepare_clause_count
  have hclauses := CompactSize.reduce_clause_count_polynomial mkt D hD φ hφ
  have hvars := CompactReduction.reduce_variable_bound mkt D hD ℓ φ hφ
  have henvelope := quadratic_envelope m A ℓ
  have hprep : φ.prepare.clauses.length ≤
      (A + A * A + 2 * ℓ + 8) * (m + 2) ^ 2 := by
    apply hc.trans
    apply le_trans _ henvelope
    dsimp [A] at *
    nlinarith
  have hlit := φ.prepare.literalCount_le (max (2 * ℓ) 2)
    (φ.prepare_width (2 * ℓ) (CompactReduction.reduce_width mkt D hD ℓ φ hφ))
  calc
    φ.prepare.literalCount ≤ φ.prepare.clauses.length * max (2 * ℓ) 2 := hlit
    _ ≤ ((A + A * A + 2 * ℓ + 8) * (m + 2) ^ 2) * max (2 * ℓ) 2 :=
      Nat.mul_le_mul_right _ hprep
    _ = sizeConstant D * (m + 2) ^ 2 := by
      dsimp [sizeConstant, A, ℓ]
      ring

private theorem sum_le_length_mul {α : Type*} (xs : List α) (f : α → Nat) (K : Nat)
    (h : ∀ x ∈ xs, f x ≤ K) : (xs.map f).sum ≤ xs.length * K := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem total_prepared_literals {ε : ℝ} (hε : 0 < ε) :
    ∃ (D : Nat) (hD : 0 < D), ∃ a : Nat,
      ∀ n : Nat, 1 ≤ n → ∀ mkt : MarriageMarket (Fin n) (Fin n),
        (((CompactReduction.reduce mkt D hD (CompactSize.bitWidth D)).map
          (fun φ => φ.prepare.literalCount)).sum : ℝ) ≤
            (a : ℝ) * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨D, hD, hbranch⟩ := CountingRates.exists_block_length hε
  obtain ⟨b, hb⟩ := CountingRates.polynomial_overhead_budget 2 D hε hbranch
  refine ⟨D, hD, sizeConstant D * b, ?_⟩
  intro n hn mkt
  let formulas := CompactReduction.reduce mkt D hD (CompactSize.bitWidth D)
  have hsum := sum_le_length_mul formulas (fun φ => φ.prepare.literalCount)
    (sizeConstant D * (n + 2) ^ 2) (prepared_literal_bound mkt D hD)
  have hsumR : ((formulas.map (fun φ => φ.prepare.literalCount)).sum : ℝ) ≤
      (formulas.length : ℝ) * (sizeConstant D : ℝ) * ((n : ℝ) + 2) ^ 2 := by
    have hcast : (((formulas.map (fun φ => φ.prepare.literalCount)).sum : Nat) : ℝ) ≤
        ((formulas.length * (sizeConstant D * (n + 2) ^ 2) : Nat) : ℝ) := by
      exact_mod_cast hsum
    push_cast at hcast
    simpa only [List.map_map, Function.comp_def, mul_assoc] using hcast
  have hpoly := hb n formulas
    (CompactReduction.reduce_query_bound mkt D hD _ (by omega) (by omega))
  have hnonneg : (0 : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hpoly (Nat.cast_nonneg (sizeConstant D))
  change ((formulas.map (fun φ => φ.prepare.literalCount)).sum : ℝ) ≤ _
  push_cast
  nlinarith

end StableMatching.ReductionSize
