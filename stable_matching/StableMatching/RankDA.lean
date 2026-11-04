import StableMatching.RankChoiceComplexity
import ToTuring.Lib.Unary
import MathEconLib.Matching.Classical.Marriage.DeferredAcceptanceComputable

/-! A list implementation of simultaneous deferred acceptance on rank inputs.
The polynomial-time claims below use actual multi-stack-machine fragments.
Agreement with the existing MathEconLib algorithm is proved separately. -/

namespace StableMatching.RankDA

open MathEconLib.Matching.MarriageMarket
open Groundwork
open RankInputComplexity

abbrev Rows := List (List Nat)
abbrev Contracts := List (Nat × Nat)
abbrev Input := Rows × Rows

def participants (rows : Rows) : List Nat := List.range rows.length
def pairs (rows : Rows) : Contracts := (participants rows).product (participants rows)

def available (rows : Rows) (rejected : Contracts) (m : Nat) : List Nat :=
  (participants rows).filter (fun w => !(rejected.elem (m, w)))

def proposals (rows : Rows) (rejected : Contracts) : Contracts :=
  (pairs rows).filter (fun p =>
    rankBest rows p.1 rows.length (available rows rejected p.1) == p.2)

def suitors (proposed : Contracts) (w : Nat) : List Nat :=
  ((proposed.filter (fun p => p.2 == w)).map Prod.fst)

def held (women : Rows) (n : Nat) (proposed : Contracts) : Contracts :=
  proposed.filter (fun p => rankBest women p.2 n (suitors proposed p.2) == p.1)

def step (input : Input) (rejected : Contracts) : Contracts :=
  let proposed := proposals input.1 rejected
  let heldNow := held input.2 input.1.length proposed
  (pairs input.1).filter (fun p =>
    rejected.elem p || (proposed.elem p && !(heldNow.elem p)))

/-- Exactly n² simultaneous rejection rounds, using a unary list as fuel. -/
def rejected (input : Input) : Contracts :=
  (pairs input.1).foldl (fun R _ => step input R) []

def output (input : Input) : Contracts :=
  held input.2 input.1.length (proposals input.1 (rejected input))

@[fun_prop] theorem participants_polyT {α : Type} [Enc α] {rows : α → Rows}
    (hrows : PolyT rows) : PolyT (fun x => participants (rows x)) := by
  exact Groundwork.PolyT.range (Groundwork.Unary.of_length hrows)

@[fun_prop] theorem pairs_polyT {α : Type} [Enc α] {rows : α → Rows}
    (hrows : PolyT rows) : PolyT (fun x => pairs (rows x)) := by
  unfold pairs
  fun_prop

@[fun_prop] theorem available_polyT {α : Type} [Enc α]
    {rows : α → Rows} {R : α → Contracts} {m : α → Nat}
    (hrows : PolyT rows) (hR : PolyT R) (hm : PolyT m) :
    PolyT (fun x => available (rows x) (R x) (m x)) := by
  unfold available
  fun_prop

@[fun_prop] theorem proposals_polyT {α : Type} [Enc α]
    {rows : α → Rows} {R : α → Contracts} (hrows : PolyT rows) (hR : PolyT R) :
    PolyT (fun x => proposals (rows x) (R x)) := by
  unfold proposals
  fun_prop

@[fun_prop] theorem suitors_polyT {α : Type} [Enc α]
    {P : α → Contracts} {w : α → Nat} (hP : PolyT P) (hw : PolyT w) :
    PolyT (fun x => suitors (P x) (w x)) := by
  unfold suitors
  fun_prop

@[fun_prop] theorem held_polyT {α : Type} [Enc α]
    {women : α → Rows} {n : α → Nat} {P : α → Contracts}
    (hwomen : PolyT women) (hn : PolyT n) (hP : PolyT P) :
    PolyT (fun x => held (women x) (n x) (P x)) := by
  unfold held
  fun_prop

@[fun_prop] theorem step_polyT {α : Type} [Enc α]
    {input : α → Input} {R : α → Contracts} (hinput : PolyT input) (hR : PolyT R) :
    PolyT (fun x => step (input x) (R x)) := by
  unfold step
  fun_prop

private theorem len_filter_le {α : Type} [Enc α] (xs : List α) (p : α → Bool) :
    Groundwork.len (xs.filter p) ≤ Groundwork.len xs := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    cases hp : p x <;> simp [hp, Groundwork.len_cons] at * <;> omega

theorem step_len (input : Input) (R : Contracts) :
    Groundwork.len (step input R) ≤ Groundwork.len (pairs input.1) := by
  exact len_filter_le _ _

theorem rejected_polyT : PolyT rejected := by
  have hp : PolyT (fun input : Input => pairs input.1) := by fun_prop
  obtain ⟨s, hs, _, hlen⟩ := Groundwork.PolyT.len_bound hp
  unfold rejected
  refine Groundwork.PolyT.foldl_add (g := fun input R (_ : Nat × Nat) => step input R)
    hp (by fun_prop) (by fun_prop) ⟨s, hs, ?_⟩
  intro input R p _
  have h := (step_len input R).trans (hlen input)
  omega

theorem output_polyT : PolyT output := by
  have hr := rejected_polyT
  unfold output
  fun_prop

end StableMatching.RankDA
