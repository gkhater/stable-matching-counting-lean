import StableMatching.CompactReduction
import StableMatching.CompactRates

/-!
# Explicit size bounds for the compact chain-cut reduction

The bit width is executable and minimal. Every residual formula has a
polynomial number of clauses in the market size and chosen block length.
-/

namespace StableMatching.CompactSize

open MathEconLib.Matching
open StoppedCounting

/-- The executable number of bits needed for a cut in a block of length at
most `D`. -/
def bitWidth (D : Nat) : Nat := Nat.clog 2 (D + 1)

theorem bitWidth_pos {D : Nat} (hD : 0 < D) : 0 < bitWidth D := by
  exact Nat.clog_pos Nat.one_lt_two (by omega)

theorem bitWidth_capacity (D : Nat) : D + 1 ≤ 2 ^ bitWidth D := by
  exact Nat.le_pow_clog Nat.one_lt_two (D + 1)

/-- The power of two at the chosen width is less than twice the domain size. -/
theorem bitWidth_pow_le_twice {D : Nat} (hD : 0 < D) :
    2 ^ bitWidth D ≤ 2 * (D + 1) := by
  have hpos := bitWidth_pos hD
  have hpred : 2 ^ (bitWidth D - 1) < D + 1 := by
    exact Nat.pow_pred_clog_lt_self Nat.one_lt_two (by omega)
  have hstep : 2 ^ bitWidth D = 2 * 2 ^ (bitWidth D - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ bitWidth D)]
    rw [pow_succ]
    omega
  rw [hstep]
  exact Nat.mul_le_mul_left 2 hpred.le

/-- The upper logarithm never uses more bits than the number of cut values. -/
theorem bitWidth_le (D : Nat) : bitWidth D ≤ D + 1 := by
  apply Nat.clog_le_of_le_pow
  exact (Nat.lt_pow_self Nat.one_lt_two).le

variable {m n : Nat} (mkt : MarriageMarket (Fin m) (Fin n))

/-- Clause count of a single residual encoded from explicit chain blocks. -/
theorem encode_clause_count (D : Nat) (hD : 0 < D) (ℓ : Nat)
    (remaining : List (Fin (indexSize mkt))) (hnd : remaining.Nodup)
    (hsmall : remaining.length ≤ m * D) :
    (MatchingPartition.encode mkt D hD ℓ remaining hnd).clauses.length ≤
      (m * D) * 2 ^ ℓ + ((m * D) * 2 ^ ℓ) * ((m * D) * 2 ^ ℓ) := by
  letI : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  letI : PartialOrder (Fin (indexSize mkt)) := indexOrder mkt
  letI := indexDecidableLE mkt
  have hbase := (MatchingPartition.partition mkt D hD remaining hnd).encode_clause_count_length ℓ
  have hq : remaining.length * 2 ^ ℓ ≤ (m * D) * 2 ^ ℓ :=
    Nat.mul_le_mul_right _ hsmall
  calc
    (MatchingPartition.encode mkt D hD ℓ remaining hnd).clauses.length ≤
        remaining.length * 2 ^ ℓ +
          (remaining.length * 2 ^ ℓ) * (remaining.length * 2 ^ ℓ) := hbase
    _ ≤ (m * D) * 2 ^ ℓ + ((m * D) * 2 ^ ℓ) * ((m * D) * 2 ^ ℓ) :=
      Nat.add_le_add hq (Nat.mul_le_mul hq hq)

/-- Every formula emitted by the actual computed matching reduction obeys
the clause bound from its small residual. -/
theorem reduce_clause_count (D : Nat) (hD : 0 < D) (ℓ : Nat) :
    ∀ φ ∈ CompactReduction.reduce mkt D hD ℓ,
      φ.clauses.length ≤
        (m * D) * 2 ^ ℓ + ((m * D) * 2 ^ ℓ) * ((m * D) * 2 ^ ℓ) := by
  letI : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  letI : Preorder (Fin (indexSize mkt)) := (indexOrder mkt).toPreorder
  letI := indexDecidableLE mkt
  intro φ hφ
  obtain ⟨leaf, _, rfl⟩ := List.mem_map.mp hφ
  exact encode_clause_count mkt D hD ℓ leaf.1 _
    ((BranchTree.build (m * D) (List.finRange (indexSize mkt))).2.leaves_small leaf.1 leaf.2)

/-- At the chosen bit width the per-leaf clause count is polynomial in
`m` and `D`. -/
theorem reduce_clause_count_polynomial (D : Nat) (hD : 0 < D) :
    ∀ φ ∈ CompactReduction.reduce mkt D hD (bitWidth D),
      φ.clauses.length ≤
        (m * D) * (2 * (D + 1)) +
          ((m * D) * (2 * (D + 1))) * ((m * D) * (2 * (D + 1))) := by
  intro φ hφ
  have hbase := reduce_clause_count mkt D hD (bitWidth D) φ hφ
  have hq : (m * D) * 2 ^ bitWidth D ≤ (m * D) * (2 * (D + 1)) :=
    Nat.mul_le_mul_left _ (bitWidth_pow_le_twice hD)
  exact hbase.trans (Nat.add_le_add hq (Nat.mul_le_mul hq hq))

end StableMatching.CompactSize
