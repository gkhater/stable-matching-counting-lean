import StableMatching.RawTraversalCorrect
import StableMatching.ParticipantBounds
import ToTuring.Poly.Basic
import StableMatching.EncodingBounds

/-! Costed traversal of the actual deferred-acceptance irreducible poset. -/

namespace StableMatching.RankTraversal

open Groundwork MathEconLib.Matching MathEconLib.Matching.MarriageMarket
open RankDA StoppedCounting

def input (D : Nat) (raw : RankDA.Input) : RawTraversal.Input :=
  (orderRows raw, raw.1.length * D, List.range (irreducibleCodes raw).length)

theorem input_polyT (D : Nat) : PolyT (input D) := by
  have hm := orderRows_polyT
  have hc := irreducibleCodes_polyT
  have hr := PolyT.range (Unary.of_length hc)
  unfold input
  fun_prop

def machine (D : Nat) : Stepped RankDA.Input (List (List Nat)) :=
  Stepped.mapIn (input D) RawTraversal.machine

@[instance_reducible] def machine_isPolyT (D : Nat) : IsPolyT (machine D) := by
  letI := RawTraversal.machine_isPolyT
  exact IsPolyT.mapIn (input_polyT D)

def tree (p : RankInput) (D : Nat) : BranchTree.Tree (Fin (indexSize p.market)) := by
  let : LE (Fin (indexSize p.market)) := (indexOrder p.market).toLE
  let : Preorder (Fin (indexSize p.market)) := (indexOrder p.market).toPreorder
  let := indexDecidableLE p.market
  exact (BranchTree.build (p.men.length * D) (List.finRange (indexSize p.market))).1

theorem initial_eq (p : RankInput) :
    List.range (irreducibleCodes (p.men, p.women)).length =
      (List.finRange (indexSize p.market)).map Fin.val := by
  rw [irreducibleCodes_correct, List.length_map, range_eq_map_finRange]
  rfl

theorem tree_correct (p : RankInput) (D : Nat) :
    RawBranching.build (orderRows (p.men, p.women)) (p.men.length * D)
      (List.range (irreducibleCodes (p.men, p.women)).length) =
      RawBranching.mapTree Fin.val (tree p D) := by
  let : LE (Fin (indexSize p.market)) := (indexOrder p.market).toLE
  let : Preorder (Fin (indexSize p.market)) := (indexOrder p.market).toPreorder
  let := indexDecidableLE p.market
  rw [initial_eq]
  apply RawBranching.build_map _ Fin.val Fin.val_injective
  intro i j
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.decide_iff]
  exact orderRows_entry p i j

theorem nodes_bound (p : RankInput) (D : Nat) (hn : 0 < p.men.length) (hD : 0 < D) :
    RawBranching.nodes (tree p D) < 2 ^ (3 + 8 * p.men.length / D) := by
  have hleaf := reduce_participant_query_bound p.market D hn hn hD
  have hnodes := RawBranching.nodes_add_one (tree p D)
  have hlen : (tree p D).leaves.length ≤ 2 ^ (2 + 8 * p.men.length / D) := by
    simpa only [StoppedCounting.reduce, ResidualEncoding.reduce, List.length_map, tree] using hleaf
  have hpow : 2 ^ (3 + 8 * p.men.length / D) = 2 * 2 ^ (2 + 8 * p.men.length / D) := by
    rw [show 3 + 8 * p.men.length / D = (2 + 8 * p.men.length / D) + 1 by omega,
      Nat.pow_succ, Nat.mul_comm]
  rw [hpow]
  omega

theorem machine_runs (p : RankInput) (D : Nat) :
    (machine D).Runs (p.men, p.women)
      (RawBranching.nodes (tree p D))
      (RawTraversal.bound (orderRows (p.men, p.women)) (p.men.length * D)
        (List.range (irreducibleCodes (p.men, p.women)).length)
        (RawBranching.nodes (tree p D)))
      ((tree p D).leaves.map (List.map Fin.val)) := by
  have h := RawTraversal.machine_runs (orderRows (p.men, p.women)) (p.men.length * D)
    (List.range (irreducibleCodes (p.men, p.women)).length)
  rw [tree_correct, RawBranching.mapTree_leaves, RawBranching.mapTree_nodes] at h
  exact Stepped.mapIn_runs h

theorem state_bound_le_word (raw : RawTraversal.Input) (budget : Nat) :
    RawTraversal.bound raw.1 raw.2.1 raw.2.2 budget ≤
      (budget + 2) * (len raw + 2) := by
  have hs := EncodingBounds.size_traversal_input_le_len raw
  simp only [size_prod] at hs
  unfold RawTraversal.bound
  nlinarith

/-- A single fixed polynomial controls preprocessing and each traversal state;
the only nonpolynomial factor is the proved number of tree nodes. -/
theorem machine_runs_polynomial_size (D : Nat) :
    ∃ q : Nat → Nat, PB q ∧ Monotone q ∧ ∀ p : RankInput,
      (machine D).Runs (p.men, p.women) (RawBranching.nodes (tree p D))
        ((RawBranching.nodes (tree p D) + 2) * (q (len (p.men, p.women)) + 2))
        ((tree p D).leaves.map (List.map Fin.val)) := by
  obtain ⟨q, hq, hmono, hlen⟩ := PolyT.len_bound (input_polyT D)
  refine ⟨q, hq, hmono, fun p => (machine_runs p D).mono le_rfl ?_⟩
  have hb := state_bound_le_word (input D (p.men, p.women)) (RawBranching.nodes (tree p D))
  exact hb.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hlen (p.men, p.women)) 2))

end StableMatching.RankTraversal

#print axioms StableMatching.RankTraversal.machine_isPolyT
#print axioms StableMatching.RankTraversal.machine_runs_polynomial_size
#print axioms StableMatching.RankTraversal.nodes_bound
