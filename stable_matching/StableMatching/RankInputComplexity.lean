import MathEconLib.Matching.Classical.Marriage.RankInput
import ToTuring.Lib.List3

/-! Verified polynomial-time preference lookups for explicit rank-list input.
These use the original multi-stack-machine `PolyT` notion and its proved
list/natural-number closure lemmas. They are the comparison primitives for
a future costed matching compiler, not a cost theorem for the whole compiler. -/

namespace StableMatching.RankInputComplexity

open MathEconLib.Matching.MarriageMarket
open Groundwork

@[fun_prop] theorem rankAt_polyT {α : Type} [Enc α]
    {rows : α → List (List Nat)} {i j : α → Nat}
    (hrows : PolyT rows) (hi : PolyT i) (hj : PolyT j) :
    PolyT (fun x => rankAt (rows x) (i x) (j x)) := by
  unfold rankAt
  fun_prop

def compareRanks (p : List (List Nat) × Nat × Nat × Nat) : Bool :=
  decide (rankAt p.1 p.2.1 p.2.2.1 ≤ rankAt p.1 p.2.1 p.2.2.2)

theorem compareRanks_polyT : PolyT compareRanks := by
  unfold compareRanks
  fun_prop

theorem decide_leM_eq (p : RankInput) (m : Fin p.men.length)
    (a b : Option (Fin p.men.length)) :
    @decide (p.market.leM m a b) ((p.market.prefM m).toDecidableLE a b) =
      compareRanks (p.men, m.val, (optionIndex a).val, (optionIndex b).val) := by
  let : Decidable (p.market.leM m a b) := (p.market.prefM m).toDecidableLE a b
  exact decide_eq_decide.mpr (p.leM_iff m a b)

theorem decide_leW_eq (p : RankInput) (w : Fin p.men.length)
    (a b : Option (Fin p.men.length)) :
    @decide (p.market.leW w a b) ((p.market.prefW w).toDecidableLE a b) =
      compareRanks (p.women, w.val, (optionIndex a).val, (optionIndex b).val) := by
  let : Decidable (p.market.leW w a b) := (p.market.prefW w).toDecidableLE a b
  exact decide_eq_decide.mpr (p.leW_iff w a b)

end StableMatching.RankInputComplexity
