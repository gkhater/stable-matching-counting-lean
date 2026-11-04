import StableMatching.RankPosetMatrix
import StableMatching.BranchTree

/-! Polynomial-time primitives for branching on an explicit order matrix. -/

namespace StableMatching.RawBranching

open Groundwork

abbrev Matrix := List (List Bool)

def leTest (matrix : Matrix) (x y : Nat) : Bool := (matrix.getD x []).getD y false
def downSize (matrix : Matrix) (remaining : List Nat) (p : Nat) : Nat :=
  (remaining.filter (fun x => leTest matrix x p)).length
def upSize (matrix : Matrix) (remaining : List Nat) (p : Nat) : Nat :=
  (remaining.filter (fun x => leTest matrix p x)).length
def score (matrix : Matrix) (remaining : List Nat) (p : Nat) : Nat :=
  min (downSize matrix remaining p) (upSize matrix remaining p)
def pivot (matrix : Matrix) (remaining : List Nat) : Option Nat := remaining.argmax (score matrix remaining)

/-- Removing the pivot explicitly makes the raw program total on malformed matrices too. -/
def includeResidual (matrix : Matrix) (remaining : List Nat) (p : Nat) : List Nat :=
  remaining.filter (fun x => (x != p) && !(leTest matrix x p))
def excludeResidual (matrix : Matrix) (remaining : List Nat) (p : Nat) : List Nat :=
  remaining.filter (fun x => (x != p) && !(leTest matrix p x))

@[fun_prop] theorem leTest_polyT {α : Type} [Enc α]
    {matrix : α → Matrix} {x y : α → Nat} (hm : PolyT matrix) (hx : PolyT x) (hy : PolyT y) :
    PolyT (fun a => leTest (matrix a) (x a) (y a)) := by unfold leTest; fun_prop

@[fun_prop] theorem downSize_polyT {α : Type} [Enc α]
    {matrix : α → Matrix} {remaining : α → List Nat} {p : α → Nat}
    (hm : PolyT matrix) (hr : PolyT remaining) (hp : PolyT p) :
    PolyT (fun a => downSize (matrix a) (remaining a) (p a)) := by unfold downSize; fun_prop

@[fun_prop] theorem upSize_polyT {α : Type} [Enc α]
    {matrix : α → Matrix} {remaining : α → List Nat} {p : α → Nat}
    (hm : PolyT matrix) (hr : PolyT remaining) (hp : PolyT p) :
    PolyT (fun a => upSize (matrix a) (remaining a) (p a)) := by unfold upSize; fun_prop

@[fun_prop] theorem score_polyT {α : Type} [Enc α]
    {matrix : α → Matrix} {remaining : α → List Nat} {p : α → Nat}
    (hm : PolyT matrix) (hr : PolyT remaining) (hp : PolyT p) :
    PolyT (fun a => score (matrix a) (remaining a) (p a)) := by unfold score; fun_prop

theorem argmax_polyT {α : Type} [Enc α] {xs : α → List Nat} {f : α → Nat → Nat}
    (hxs : PolyT xs) (hf : PolyT (fun p : α × Nat => f p.1 p.2)) :
    PolyT (fun a => (xs a).argmax (f a)) := by
  obtain ⟨s, hs, _, hlen⟩ := Groundwork.PolyT.len_bound hxs
  unfold List.argmax
  refine Groundwork.PolyT.foldl_add (g := fun a => List.argAux (fun b c => f a c < f a b))
    hxs (by fun_prop) ?_ ⟨fun n => s n + 4, hs.add (PB.const 4), ?_⟩
  · have h : PolyT (fun p : α × Option Nat × Nat => p.2.1.elim (some p.2.2)
        (fun c => if f p.1 c < f p.1 p.2.2 then some p.2.2 else some c)) := by fun_prop
    exact h.congr (fun p => by rcases p with ⟨a, o, e⟩; cases o <;> rfl)
  · intro a current e he
    have hsize := (Groundwork.len_le_of_mem he).trans (hlen a)
    cases current with
    | none => simp only [List.argAux, Groundwork.len_some, Groundwork.len_none]; omega
    | some c =>
      change Groundwork.len (if f a c < f a e then some e else some c) ≤ _
      split_ifs <;> simp only [Groundwork.len_some] <;> omega

@[fun_prop] theorem pivot_polyT {α : Type} [Enc α]
    {matrix : α → Matrix} {remaining : α → List Nat} (hm : PolyT matrix) (hr : PolyT remaining) :
    PolyT (fun a => pivot (matrix a) (remaining a)) := by
  exact argmax_polyT hr (by fun_prop)

@[fun_prop] theorem includeResidual_polyT {α : Type} [Enc α]
    {matrix : α → Matrix} {remaining : α → List Nat} {p : α → Nat}
    (hm : PolyT matrix) (hr : PolyT remaining) (hp : PolyT p) :
    PolyT (fun a => includeResidual (matrix a) (remaining a) (p a)) := by
  unfold includeResidual
  fun_prop

@[fun_prop] theorem excludeResidual_polyT {α : Type} [Enc α]
    {matrix : α → Matrix} {remaining : α → List Nat} {p : α → Nat}
    (hm : PolyT matrix) (hr : PolyT remaining) (hp : PolyT p) :
    PolyT (fun a => excludeResidual (matrix a) (remaining a) (p a)) := by
  unfold excludeResidual
  fun_prop

theorem include_length_lt (matrix : Matrix) (remaining : List Nat) (p : Nat) (hp : p ∈ remaining) :
    (includeResidual matrix remaining p).length < remaining.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨p, hp, by simp⟩

theorem exclude_length_lt (matrix : Matrix) (remaining : List Nat) (p : Nat) (hp : p ∈ remaining) :
    (excludeResidual matrix remaining p).length < remaining.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨p, hp, by simp⟩

end StableMatching.RawBranching
