import StableMatching.RankInputComplexity
import MathEconLib.Matching.Classical.Marriage.RankChoice

/-! Polynomial-time multi-stack-machine fragments for rank-list choice. -/

namespace StableMatching.RankInputComplexity

open MathEconLib.Matching.MarriageMarket
open Groundwork

@[fun_prop] theorem preferHigher_polyT {α : Type} [Enc α]
    {rows : α → List (List Nat)} {i best candidate : α → Nat}
    (hrows : PolyT rows) (hi : PolyT i) (hbest : PolyT best) (hcandidate : PolyT candidate) :
    PolyT (fun x => preferHigher (rankAt (rows x) (i x)) (best x) (candidate x)) := by
  unfold preferHigher
  fun_prop

@[fun_prop] theorem rankBest_polyT {α : Type} [Enc α]
    {rows : α → List (List Nat)} {i outside : α → Nat} {candidates : α → List Nat}
    (hrows : PolyT rows) (hi : PolyT i) (houtside : PolyT outside)
    (hcandidates : PolyT candidates) :
    PolyT (fun x => rankBest (rows x) (i x) (outside x) (candidates x)) := by
  obtain ⟨s, hs, _, hlen⟩ := Groundwork.PolyT.len_bound hcandidates
  unfold rankBest
  refine Groundwork.PolyT.foldl_add (g := fun x => preferHigher (rankAt (rows x) (i x)))
    hcandidates houtside (by fun_prop) ⟨s, hs, ?_⟩
  intro x best candidate hcandidate
  have he := (Groundwork.len_le_of_mem hcandidate).trans (hlen x)
  rcases preferHigher_mem (rankAt (rows x) (i x)) best candidate with h | h
  · rw [h]
    omega
  · rw [h]
    omega

end StableMatching.RankInputComplexity
