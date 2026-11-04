import StableMatching.MatchingPartition
import StableMatching.ParticipantBounds

/-! An executable compact reduction, including the computed leaf partitions. -/

namespace StableMatching.CompactReduction

open MathEconLib.Matching
open StoppedCounting

variable {m n : Nat} (mkt : MarriageMarket (Fin m) (Fin n))

def reduce (D : Nat) (hD : 0 < D) (ℓ : Nat) : List CNF := by
  letI : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  letI : Preorder (Fin (indexSize mkt)) := (indexOrder mkt).toPreorder
  letI := indexDecidableLE mkt
  let tree := BranchTree.build (m * D) (List.finRange (indexSize mkt))
  exact tree.1.leaves.attach.map (fun leaf =>
    MatchingPartition.encode mkt D hD ℓ leaf.1
      (tree.2.leaves_nodup (List.nodup_finRange _) leaf.1 leaf.2))

theorem reduce_correct (D : Nat) (hD : 0 < D) (ℓ : Nat) (hcap : D + 1 ≤ 2 ^ ℓ) :
    ((reduce mkt D hD ℓ).map CNF.satCount).sum = Nat.card mkt.StableMatching := by
  let : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  let : Preorder (Fin (indexSize mkt)) := (indexOrder mkt).toPreorder
  let := indexDecidableLE mkt
  let tree := BranchTree.build (m * D) (List.finRange (indexSize mkt))
  have hleaf : ((reduce mkt D hD ℓ).map CNF.satCount).sum =
      (tree.1.leaves.map BranchTree.count).sum := by
    unfold reduce
    simp only [List.map_map, Function.comp_def]
    have heq :
        (tree.1.leaves.attach.map (fun leaf =>
          (MatchingPartition.encode mkt D hD ℓ leaf.1
            (tree.2.leaves_nodup (List.nodup_finRange _) leaf.1 leaf.2)).satCount)) =
        tree.1.leaves.attach.map (fun leaf => BranchTree.count leaf.1) := by
      apply List.map_congr_left
      intro leaf _
      exact MatchingPartition.encode_correct mkt D hD ℓ hcap leaf.1 _
    change (tree.1.leaves.attach.map _).sum = _
    rw [heq]
    simp
  have hcount : ((reduce mkt D hD ℓ).map CNF.satCount).sum =
      Nat.card (LowerSet (Fin (indexSize mkt))) :=
    hleaf.trans (tree.2.count_preserving.trans
      (ResidualEncoding.count_eq_of_exhaustive _ (fun _ => List.mem_finRange _)))
  let e : Fin (indexSize mkt) ≃o {μ : mkt.StableMatching // SupIrred μ} :=
    mkt.computedIrreducibleOrderIso (List.finRange m) (List.finRange n)
      (fun _ => List.mem_finRange _) (fun _ => List.mem_finRange _)
  exact hcount.trans
    (Nat.card_congr ((MarriageMarket.StableMatching.lowerSetSupIrred mkt).toEquiv.trans
      (LowerSet.map e.symm).toEquiv)).symm

theorem reduce_variable_bound (D : Nat) (hD : 0 < D) (ℓ : Nat) :
    ∀ φ ∈ reduce mkt D hD ℓ, φ.numVars ≤ 2 * m * ℓ := by
  let : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  let : Preorder (Fin (indexSize mkt)) := (indexOrder mkt).toPreorder
  let := indexDecidableLE mkt
  intro φ hφ
  obtain ⟨leaf, _, rfl⟩ := List.mem_map.mp hφ
  exact MatchingPartition.encode_variable_bound mkt D hD ℓ leaf.1 _
    ((BranchTree.build (m * D) (List.finRange (indexSize mkt))).2.leaves_small leaf.1 leaf.2)

theorem reduce_width (D : Nat) (hD : 0 < D) (ℓ : Nat) :
    ∀ φ ∈ reduce mkt D hD ℓ, ∀ clause ∈ φ.clauses, clause.length ≤ 2 * ℓ := by
  intro φ hφ
  obtain ⟨leaf, _, rfl⟩ := List.mem_map.mp hφ
  exact MatchingPartition.encode_width mkt D hD ℓ leaf.1 _

theorem reduce_length (D : Nat) (hD : 0 < D) (ℓ : Nat) :
    (reduce mkt D hD ℓ).length = (StoppedCounting.reduce mkt (m * D)).length := by
  simp only [reduce, List.length_map, List.length_attach, StoppedCounting.reduce,
    ResidualEncoding.reduce]

theorem reduce_query_bound (D : Nat) (hD : 0 < D) (ℓ : Nat)
    (hm : 0 < m) (hn : 0 < n) :
    (reduce mkt D hD ℓ).length ≤ 2 ^ (2 + 8 * n / D) := by
  rw [reduce_length]
  exact reduce_participant_query_bound mkt D hm hn hD

end StableMatching.CompactReduction
