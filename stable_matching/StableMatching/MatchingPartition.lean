import StableMatching.StoppedCounting
import StableMatching.BlockPartition
import MathEconLib.Matching.Classical.Marriage.ComputedBlocks

/-! Compact chain-cut encodings of the actual computed matching residuals. -/

namespace StableMatching.MatchingPartition

open MathEconLib.Matching
open StoppedCounting

variable {m n : Nat} (mkt : MarriageMarket (Fin m) (Fin n))

/-- Explicit blocks, with their order inherited from stable matchings. -/
def partition (D : Nat) (hD : 0 < D)
    (remaining : List (Fin (indexSize mkt))) (hnd : remaining.Nodup) :
    @BlockPartition.Data (Fin (indexSize mkt)) (indexOrder mkt) inferInstance D := by
  letI : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  letI : PartialOrder (Fin (indexSize mkt)) := indexOrder mkt
  refine {
    remaining := remaining
    blocks := mkt.rowBlocks D remaining
    remaining_nodup := hnd
    flatten_perm := mkt.rowBlocks_perm D hD remaining hnd
    block_nonempty := mkt.rowBlocks_nonempty D remaining
    block_length_le := mkt.rowBlocks_length_le D remaining
    block_pairwise := ?_ }
  intro block hb
  apply (mkt.rowBlocks_pairwise D remaining block hb).imp
  intro i j hij
  exact (MarriageMarket.StableMatching.le_iff_menWeaklyPrefer mkt).mp hij

def encode (D : Nat) (hD : 0 < D) (ℓ : Nat)
    (remaining : List (Fin (indexSize mkt))) (hnd : remaining.Nodup) : CNF :=
  letI : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  letI : PartialOrder (Fin (indexSize mkt)) := indexOrder mkt
  letI := indexDecidableLE mkt
  (partition mkt D hD remaining hnd).encode ℓ

theorem encode_correct (D : Nat) (hD : 0 < D) (ℓ : Nat) (hcap : D + 1 ≤ 2 ^ ℓ)
    (remaining : List (Fin (indexSize mkt))) (hnd : remaining.Nodup) :
    (encode mkt D hD ℓ remaining hnd).satCount =
      @BranchTree.count (Fin (indexSize mkt)) (indexOrder mkt).toPreorder remaining := by
  let : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  let : PartialOrder (Fin (indexSize mkt)) := indexOrder mkt
  let := indexDecidableLE mkt
  exact (partition mkt D hD remaining hnd).encode_correct hcap

theorem encode_variable_bound (D : Nat) (hD : 0 < D) (ℓ : Nat)
    (remaining : List (Fin (indexSize mkt))) (hnd : remaining.Nodup)
    (hsmall : remaining.length ≤ m * D) :
    (encode mkt D hD ℓ remaining hnd).numVars ≤ 2 * m * ℓ := by
  let : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  let : PartialOrder (Fin (indexSize mkt)) := indexOrder mkt
  let := indexDecidableLE mkt
  change ((partition mkt D hD remaining hnd).encode ℓ).numVars ≤ _
  rw [BlockPartition.Data.encode_numVars]
  exact Nat.mul_le_mul_right ℓ (mkt.rowBlocks_count_le_twice D hD remaining hsmall)

theorem encode_width (D : Nat) (hD : 0 < D) (ℓ : Nat)
    (remaining : List (Fin (indexSize mkt))) (hnd : remaining.Nodup) :
    ∀ clause ∈ (encode mkt D hD ℓ remaining hnd).clauses, clause.length ≤ 2 * ℓ := by
  let : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  let : PartialOrder (Fin (indexSize mkt)) := indexOrder mkt
  let := indexDecidableLE mkt
  exact (partition mkt D hD remaining hnd).encode_width ℓ

end StableMatching.MatchingPartition
