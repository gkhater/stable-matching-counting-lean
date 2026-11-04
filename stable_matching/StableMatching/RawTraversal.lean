import StableMatching.RawBranching

/-! A stepped depth-first traversal with polynomial-time start, step and readout. -/

namespace StableMatching.RawTraversal

open Groundwork
open RawBranching

abbrev Input := Matrix × Nat × List Nat
abbrev State := Matrix × Nat × List (List Nat) × List (List Nat)

def init (input : Input) : State := (input.1, input.2.1, [input.2.2], [])

def step (s : State) : State :=
  if s.2.2.1.isEmpty then s else
    let remaining := s.2.2.1.head?.getD []
    let rest := s.2.2.1.tail
    if remaining.length ≤ s.2.1 then
      (s.1, s.2.1, rest, remaining :: s.2.2.2)
    else
      let p := (pivot s.1 remaining).getD 0
      (s.1, s.2.1, includeResidual s.1 remaining p :: excludeResidual s.1 remaining p :: rest,
        s.2.2.2)

def out (s : State) : Option (List (List Nat)) :=
  if s.2.2.1.isEmpty then some s.2.2.2.reverse else none

def machine : Stepped Input (List (List Nat)) where
  σ := State
  init := init
  step := step
  out := out

theorem init_polyT : PolyT init := by unfold init; fun_prop
theorem step_polyT : PolyT step := by unfold step; fun_prop
theorem out_polyT : PolyT out := by unfold out; fun_prop

@[instance_reducible] def machine_isPolyT : IsPolyT machine where
  enc := (inferInstance : Enc State)
  carried := (inferInstance : Carried State)
  init := init_polyT
  step := step_polyT
  out := out_polyT

end StableMatching.RawTraversal
