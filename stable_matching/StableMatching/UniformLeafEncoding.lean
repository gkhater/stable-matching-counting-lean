import StableMatching.UniformQueryParameters
import StableMatching.RankBlocks
import StableMatching.RawChainCutCorrect
import StableMatching.MatchingPartition
import StableMatching.UniformTraversal
import StableMatching.UniformCounting

/-! The costed raw leaf encoder is exactly the already proved matching reduction. -/

namespace StableMatching.UniformLeafEncoding

open Groundwork MathEconLib.Matching MathEconLib.Matching.MarriageMarket
open StoppedCounting

def blocks (p : List Bool × List Nat) : RawChainCut.Blocks :=
  RankDA.rowBlocksCode (UniformQueryParameters.blockLength p.1)
    (RankInputCode.decode p.1) p.2

theorem blocks_polyT : PolyT blocks := by
  have hd := UniformQueryParameters.blockLength_polyT
  have hr := RankInputCode.decode_polyT
  exact RankDA.rowBlocksCode_polyT.comp
    (g := fun p : List Bool × List Nat =>
      (UniformQueryParameters.blockLength p.1, RankInputCode.decode p.1, p.2)) (by fun_prop)

def encode (p : List Bool × List Nat) : RawChainCut.RawCNF :=
  UniformQueryParameters.encodeLeaf (p.1, blocks p)

theorem encode_polyT : PolyT encode :=
  UniformQueryParameters.encodeLeaf_polyT.comp (PolyT.prodMk (by fun_prop) blocks_polyT)

theorem encode_eq (p : RankInput) (width : Nat)
    (hb : ∀ row ∈ p.men ++ p.women, ∀ a ∈ row, a < 2 ^ width)
    (remaining : List (Fin (indexSize p.market))) (hnd : remaining.Nodup) :
    encode (RankInputCode.encode p width, remaining.map Fin.val) =
      RawChainCut.serialize (MatchingPartition.encode p.market
        (ExecutableSchedule.blockLength p.men.length) (ExecutableSchedule.blockLength_pos _)
        (ExecutableSchedule.bitWidth p.men.length) remaining hnd) := by
  let : LE (Fin (indexSize p.market)) := (indexOrder p.market).toLE
  let : PartialOrder (Fin (indexSize p.market)) := indexOrder p.market
  let := indexDecidableLE p.market
  let D := ExecutableSchedule.blockLength p.men.length
  let ell := ExecutableSchedule.bitWidth p.men.length
  let d := MatchingPartition.partition p.market D (ExecutableSchedule.blockLength_pos _) remaining hnd
  have hdecode := RankInputCode.decode_encode p width hb
  have hn : UniformQueryParameters.n (RankInputCode.encode p width) = p.men.length := by
    unfold UniformQueryParameters.n
    rw [hdecode]
  have hm : ∀ i j : Fin (indexSize p.market),
      RawChainCut.matrixAt (RankDA.orderRows (p.men, p.women)) i.val j.val = true ↔ i ≤ j :=
    fun i j => RankDA.orderRows_entry p i j
  have hblocks : blocks (RankInputCode.encode p width, remaining.map Fin.val) =
      RawChainCut.blocksOf d Fin.val := by
    unfold blocks UniformQueryParameters.blockLength
    rw [hn, hdecode]
    dsimp only
    exact RankDA.rowBlocksCode_correct p D remaining
  unfold encode UniformQueryParameters.encodeLeaf
  rw [hblocks]
  unfold UniformQueryParameters.matrix UniformQueryParameters.domain UniformQueryParameters.bitFuel
    UniformQueryParameters.bitWidth
  rw [hdecode, hn]
  exact RawChainCut.encode_eq_blockPartition d Fin.val _ hm ell
    (List.replicate ell ()) List.length_replicate

def queries (p : List Bool × List (List Nat)) : List RawChainCut.RawCNF :=
  p.2.map (fun r => encode (p.1, r))

theorem queries_polyT : PolyT queries := by
  unfold queries
  exact PolyT.map (f := fun code : List Bool × List (List Nat) =>
    fun r : List Nat => encode (code.1, r))
    (encode_polyT.comp (g := fun p : (List Bool × List (List Nat)) × List Nat =>
      (p.1.1, p.2)) (by fun_prop))
    (PolyT.id' (α := List Bool × List (List Nat))).snd

theorem queries_eq (p : RankInput) (width : Nat)
    (hb : ∀ row ∈ p.men ++ p.women, ∀ a ∈ row, a < 2 ^ width) :
    queries (RankInputCode.encode p width, UniformTraversal.leaves p) =
      (UniformCounting.queries p.market).map RawChainCut.serialize := by
  let : LE (Fin (indexSize p.market)) := (indexOrder p.market).toLE
  let : Preorder (Fin (indexSize p.market)) := (indexOrder p.market).toPreorder
  let := indexDecidableLE p.market
  let D := ExecutableSchedule.blockLength p.men.length
  let hD := ExecutableSchedule.blockLength_pos p.men.length
  let ell := ExecutableSchedule.bitWidth p.men.length
  let t := BranchTree.build (p.men.length * D) (List.finRange (indexSize p.market))
  change (t.1.leaves.map (List.map Fin.val)).map (fun r => encode (RankInputCode.encode p width, r)) = _
  rw [List.map_map]
  calc
    _ = t.1.leaves.attach.map (fun leaf => encode (RankInputCode.encode p width, leaf.1.map Fin.val)) := by
      simp
    _ = t.1.leaves.attach.map (fun leaf => RawChainCut.serialize
        (MatchingPartition.encode p.market D hD ell leaf.1
          (t.2.leaves_nodup (List.nodup_finRange _) leaf.1 leaf.2))) := by
      apply List.map_congr_left
      intro leaf _
      exact encode_eq p width hb leaf.1 _
    _ = _ := by
      simp only [UniformCounting.queries, CompactReduction.reduce, List.map_map, Function.comp_def]
      rfl

end StableMatching.UniformLeafEncoding
