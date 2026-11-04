import StableMatching.RankDA
import MathEconLib.Matching.Classical.Marriage.RankTruncation

/-! Polynomial-time rank-list realization of threshold truncation. -/

namespace StableMatching.RankInputComplexity

open MathEconLib.Matching.MarriageMarket
open Groundwork

@[fun_prop] theorem rankBand_polyT {α : Type} [Enc α]
    {row : α → List Nat} {threshold outside i score : α → Nat}
    (hrow : PolyT row) (ht : PolyT threshold) (ho : PolyT outside)
    (hi : PolyT i) (hs : PolyT score) :
    PolyT (fun x => rankBand (row x) (threshold x) (outside x) (i x) (score x)) := by
  unfold rankBand
  fun_prop

@[fun_prop] theorem truncateRanks_polyT {α : Type} [Enc α]
    {row : α → List Nat} {threshold outside : α → Nat}
    (hrow : PolyT row) (ht : PolyT threshold) (ho : PolyT outside) :
    PolyT (fun x => truncateRanks (row x) (threshold x) (outside x)) := by
  have hrange : PolyT (fun x => List.range (row x).length) :=
    Groundwork.PolyT.range (Groundwork.Unary.of_length hrow)
  unfold truncateRanks
  fun_prop

@[fun_prop] theorem set_polyT {α β : Type} [Enc α] [Enc β]
    {xs : α → List β} {i : α → Nat} {a : α → β}
    (hxs : PolyT xs) (hi : PolyT i) (ha : PolyT a) :
    PolyT (fun x => (xs x).set (i x) (a x)) := by
  have h : PolyT (fun x => if i x < (xs x).length then
      (xs x).take (i x) ++ a x :: (xs x).drop (i x + 1) else xs x) := by fun_prop
  exact h.congr (fun _ => List.set_eq_take_append_cons_drop.symm)

@[fun_prop] theorem truncateRankRows_polyT {α : Type} [Enc α]
    {rows : α → List (List Nat)} {m threshold : α → Nat}
    (hrows : PolyT rows) (hm : PolyT m) (ht : PolyT threshold) :
    PolyT (fun x => truncateRankRows (rows x) (m x) (threshold x)) := by
  unfold truncateRankRows
  fun_prop

end StableMatching.RankInputComplexity
