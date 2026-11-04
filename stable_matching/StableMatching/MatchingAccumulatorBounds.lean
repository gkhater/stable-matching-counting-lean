import StableMatching.UniformCounting
import StableMatching.RankInputCode
import MathEconLib.Matching.Classical.Marriage.CountingBounds

/-! Binary-size bounds for partial sums in the matching SAT cursor. -/

namespace StableMatching.MatchingAccumulatorBounds

open Groundwork
open MathEconLib.Matching
open MathEconLib.Matching.MarriageMarket

private theorem sublist_sum_le {xs ys : List Nat} (h : xs.Sublist ys) :
    xs.sum ≤ ys.sum := by
  induction h with
  | slnil => simp
  | cons a h ih =>
      simpa only [List.sum_cons] using ih.trans (Nat.le_add_left _ _)
  | cons_cons a h ih =>
      simpa only [List.sum_cons] using Nat.add_le_add_left ih _

/-- Each partial sum of a list totaling the stable-matching count fits in
`n²+2` cells of the `Groundwork.size` measure. -/
theorem sublist_size_le {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (values part : List Nat) (hsum : values.sum = Nat.card mkt.StableMatching)
    (hpartial : part.Sublist values) :
    Groundwork.size part.sum ≤ n * n + 2 := by
  have hsumBound : values.sum ≤ 2 ^ (n * n) := by
    rw [hsum]
    simpa only [Fintype.card_fin] using
      MathEconLib.Matching.MarriageMarket.StableMatching.card_le_two_pow_pairs mkt
  have hpart : part.sum ≤ 2 ^ (n * n) :=
    (sublist_sum_le hpartial).trans hsumBound
  have hbits := Nat.size_le_size hpart
  rw [Nat.size_pow] at hbits
  rw [Groundwork.size_nat]
  omega

theorem prefix_size_le {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (values : List Nat) (hsum : values.sum = Nat.card mkt.StableMatching)
    (k : Nat) :
    Groundwork.size (values.take k).sum ≤ n * n + 2 :=
  sublist_size_le mkt values (values.take k) hsum (List.take_sublist _ _)

/-- The actual prepared SAT counts have the required bounded cursor. -/
theorem prepared_sublist_size_le {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (part : List Nat)
    (hpartial : part.Sublist
      ((UniformCounting.queries mkt).map
        (fun φ => MainResults.numSat φ.prepare.clauses))) :
    Groundwork.size part.sum ≤ n * n + 2 :=
  sublist_size_le mkt _ part (UniformCounting.count_correct mkt) hpartial

theorem prepared_prefix_size_le {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (k : Nat) :
    Groundwork.size
      (((UniformCounting.queries mkt).map
        (fun φ => MainResults.numSat φ.prepare.clauses)).take k).sum ≤
        n * n + 2 :=
  prefix_size_le mkt _ (UniformCounting.count_correct mkt) k

theorem market_size_le_encoded_input (p : RankInput) (width : Nat) :
    p.men.length ≤ (RankInputCode.encode p width).length := by
  rw [RankInputCode.encode_length]
  omega

/-- The same accumulator bound measured against the raw encoded input. -/
theorem sublist_size_le_encoded_input (p : RankInput) (width : Nat)
    (values part : List Nat)
    (hsum : values.sum = Nat.card p.market.StableMatching)
    (hpartial : part.Sublist values) :
    Groundwork.size part.sum ≤
      (RankInputCode.encode p width).length ^ 2 + 2 := by
  have hsize := sublist_size_le p.market values part hsum hpartial
  have hn := market_size_le_encoded_input p width
  nlinarith

theorem prepared_sublist_size_le_encoded_input (p : RankInput)
    (width : Nat) (part : List Nat)
    (hpartial : part.Sublist
      ((UniformCounting.queries p.market).map
        (fun φ => MainResults.numSat φ.prepare.clauses))) :
    Groundwork.size part.sum ≤
      (RankInputCode.encode p width).length ^ 2 + 2 :=
  sublist_size_le_encoded_input p width _ part
    (UniformCounting.count_correct p.market) hpartial

end StableMatching.MatchingAccumulatorBounds
