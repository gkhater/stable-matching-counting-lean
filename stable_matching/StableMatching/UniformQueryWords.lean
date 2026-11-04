import StableMatching.UniformLeafEncoding
import StableMatching.RawSATInput
import StableMatching.SATFormulaFold
import StableMatching.QueryPolyApplications

set_option maxHeartbeats 2000000

/-! The uniform costed constructor of the actual SAT machine's input words. -/

namespace StableMatching.UniformQueryWords

open Groundwork MathEconLib.Matching.MarriageMarket
open UniformQueryParameters

def vars (p : List Bool × List Nat) : List Unit :=
  varsFuel p.1 (UniformLeafEncoding.blocks p)

theorem vars_polyT : PolyT vars := by
  exact QueryPolyApplications.varsFuel
    (code := fun p : List Bool × List Nat => p.1) (blocks := UniformLeafEncoding.blocks)
    (PolyT.id' (α := List Bool × List Nat)).fst UniformLeafEncoding.blocks_polyT

def prepared (p : List Bool × List Nat) : RawChainCut.RawCNF :=
  RawSATInput.prepare (vars p) (UniformLeafEncoding.encode p)

theorem prepared_polyT : PolyT prepared := by
  exact QueryPolyApplications.prepare (fuel := vars) (raw := UniformLeafEncoding.encode)
    vars_polyT UniformLeafEncoding.encode_polyT

def leaf (p : List Bool × List Nat) : List Bool :=
  RawSATInput.encodeInput (widthFuel p.1) (vars p ++ List.replicate 4 ()) (prepared p)

theorem leaf_polyT : PolyT leaf := by
  have hw : PolyT (fun p : List Bool × List Nat => widthFuel p.1) :=
    widthFuel_polyT.comp (g := fun p : List Bool × List Nat => p.1) (by fun_prop)
  have hv : PolyT (fun p : List Bool × List Nat => vars p ++ List.replicate 4 ()) :=
    PolyT.append vars_polyT (PolyT.const _)
  exact QueryPolyApplications.encodeInput (width := fun p => widthFuel p.1)
    (vars := fun p => vars p ++ List.replicate 4 ()) (raw := prepared) hw hv prepared_polyT

theorem leaf_eq (p : RankInput) (width : Nat)
    (hb : ∀ row ∈ p.men ++ p.women, ∀ a ∈ row, a < 2 ^ width)
    (remaining : List (Fin (StoppedCounting.indexSize p.market))) (hnd : remaining.Nodup) :
    leaf (RankInputCode.encode p width, remaining.map Fin.val) =
      SATFormulaFold.encodeQuery p.men.length (MatchingPartition.encode p.market
        (ExecutableSchedule.blockLength p.men.length) (ExecutableSchedule.blockLength_pos _)
        (ExecutableSchedule.bitWidth p.men.length) remaining hnd) := by
  let code := RankInputCode.encode p width
  let arg := (code, remaining.map Fin.val)
  let phi := MatchingPartition.encode p.market
    (ExecutableSchedule.blockLength p.men.length) (ExecutableSchedule.blockLength_pos _)
    (ExecutableSchedule.bitWidth p.men.length) remaining hnd
  have he : UniformLeafEncoding.encode arg = RawChainCut.serialize phi :=
    UniformLeafEncoding.encode_eq p width hb remaining hnd
  have hv : (vars arg).length = phi.numVars := by
    have hh := varsFuel_length_eq_numVars code (UniformLeafEncoding.blocks arg)
    change (vars arg).length = (UniformLeafEncoding.encode arg).1 at hh
    rw [he] at hh
    exact hh
  have hn : n code = p.men.length := by
    unfold n code
    rw [RankInputCode.decode_encode p width hb]
  have hw : (widthFuel code).length = UniformCounting.width p.men.length := by
    rw [widthFuel_length]
    unfold bitWidth
    rw [hn]
    rfl
  change RawSATInput.encodeInput (widthFuel code) (vars arg ++ List.replicate 4 ())
    (RawSATInput.prepare (vars arg) (UniformLeafEncoding.encode arg)) = _
  rw [he, RawSATInput.encodeInput_prepared phi _ _ hv, hw]
  rfl

def queries (p : List Bool × List (List Nat)) : List (List Bool) :=
  p.2.map (fun r => leaf (p.1, r))

theorem queries_polyT : PolyT queries := by
  exact PolyT.map (f := fun p : List Bool × List (List Nat) =>
    fun r : List Nat => leaf (p.1, r))
    (leaf_polyT.comp (g := fun p : (List Bool × List (List Nat)) × List Nat =>
      (p.1.1, p.2)) (by fun_prop))
    (PolyT.id' (α := List Bool × List (List Nat))).snd

theorem queries_eq (p : RankInput) (width : Nat)
    (hb : ∀ row ∈ p.men ++ p.women, ∀ a ∈ row, a < 2 ^ width) :
    queries (RankInputCode.encode p width, UniformTraversal.leaves p) = SATFormulaFold.words p.market := by
  let : LE (Fin (StoppedCounting.indexSize p.market)) := (StoppedCounting.indexOrder p.market).toLE
  let : Preorder (Fin (StoppedCounting.indexSize p.market)) := (StoppedCounting.indexOrder p.market).toPreorder
  let := StoppedCounting.indexDecidableLE p.market
  let D := ExecutableSchedule.blockLength p.men.length
  let hD := ExecutableSchedule.blockLength_pos p.men.length
  let ell := ExecutableSchedule.bitWidth p.men.length
  let t := BranchTree.build (p.men.length * D) (List.finRange (StoppedCounting.indexSize p.market))
  change (t.1.leaves.map (List.map Fin.val)).map (fun r => leaf (RankInputCode.encode p width, r)) = _
  rw [List.map_map]
  calc
    _ = t.1.leaves.attach.map (fun r => leaf (RankInputCode.encode p width, r.1.map Fin.val)) := by simp
    _ = t.1.leaves.attach.map (fun r => SATFormulaFold.encodeQuery p.men.length
        (MatchingPartition.encode p.market D hD ell r.1
          (t.2.leaves_nodup (List.nodup_finRange _) r.1 r.2))) := by
      apply List.map_congr_left
      intro r _
      exact leaf_eq p width hb r.1 _
    _ = _ := by
      simp only [SATFormulaFold.words, UniformCounting.queries, CompactReduction.reduce,
        List.map_map, Function.comp_def]
      rfl

end StableMatching.UniformQueryWords
