import StableMatching.RankGenerators

/-! A polynomial-time canonical list of the actual matching irreducibles. -/

namespace StableMatching.RankDA

open MathEconLib.Matching
open MathEconLib.Matching.MarriageMarket
open Groundwork

def allCandidates (input : Input) : List (List Nat) :=
  (pairs input.1).filterMap (fun p => candidateCodes input p.1 p.2)

def irreducibleCodes (input : Input) : List (List Nat) :=
  ((allCandidates input).filter (fun codes => decide (codes ≠ bottomCodes input))).dedup

@[fun_prop] theorem allCandidates_polyT {α : Type} [Enc α] {input : α → Input}
    (hinput : PolyT input) : PolyT (fun x => allCandidates (input x)) := by
  unfold allCandidates
  fun_prop

theorem irreducibleCodes_polyT : PolyT irreducibleCodes := by
  unfold irreducibleCodes
  apply Groundwork.PolyT.dedup
  apply Groundwork.PolyT.filter
  · exact Groundwork.PolyT.decide_ne (by fun_prop) (by fun_prop)
  · fun_prop

theorem range_eq_map_finRange (n : Nat) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem <;> simp

private theorem map_product {α β γ δ : Type*} (xs : List α) (ys : List β)
    (f : α → γ) (g : β → δ) :
    (xs.map f) ×ˢ (ys.map g) = (xs ×ˢ ys).map (fun p => (f p.1, g p.2)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.product_cons, ih, List.map_map, Function.comp_def]

theorem pairs_finRange (rows : Rows) :
    pairs rows = ((List.finRange rows.length) ×ˢ (List.finRange rows.length)).map
      (fun p => (p.1.val, p.2.val)) := by
  change (List.range rows.length) ×ˢ (List.range rows.length) = _
  rw [range_eq_map_finRange, map_product]

theorem allCandidates_correct (p : RankInput) :
    allCandidates (p.men, p.women) =
      (p.market.thresholdCandidates (List.finRange p.men.length) (List.finRange p.men.length)).map
        (fun μ => matchingCodes μ.matching) := by
  unfold allCandidates MarriageMarket.thresholdCandidates
  rw [pairs_finRange]
  simp only [List.filterMap_map, List.map_filterMap, Function.comp_def]
  apply List.filterMap_congr
  intro q _
  exact candidateCodes_correct p q.1 q.2

theorem stableCodes_injective {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n)) :
    Function.Injective (fun μ : mkt.StableMatching => matchingCodes μ.matching) := by
  intro μ ν h
  apply MarriageMarket.StableMatching.ext mkt
  exact matchingCodes_injective h

theorem irreducibleCodes_correct (p : RankInput) :
    irreducibleCodes (p.men, p.women) =
      (p.market.computedIrreducibles (List.finRange p.men.length) (List.finRange p.men.length)).map
        (fun μ => matchingCodes μ.matching) := by
  let := p.market.stableMatchingDecidableEq
  have hpred (μ : p.market.StableMatching) :
      decide (matchingCodes μ.matching ≠ bottomCodes (p.men, p.women)) =
        decide (μ ≠ p.market.computedBottom) := by
    apply decide_eq_decide.mpr
    rw [bottomCodes_correct]
    apply not_congr
    exact (stableCodes_injective p.market).eq_iff (a := μ) (b := p.market.computedBottom)
  unfold irreducibleCodes
  rw [allCandidates_correct, List.filter_map]
  simp only [Function.comp_def, hpred]
  rw [List.dedup_map_of_injective (stableCodes_injective p.market)]
  rfl

end StableMatching.RankDA
