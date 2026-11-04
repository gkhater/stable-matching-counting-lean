import StableMatching.RankTraversalCode
import StableMatching.ScheduleComplexity

/-! One fixed Boolean-input traversal program with the uniform logarithmic schedule. -/

namespace StableMatching.UniformTraversal

open Groundwork MathEconLib.Matching.MarriageMarket

def rankInput (raw : RankDA.Input) : RawTraversal.Input :=
  RankTraversal.input (ExecutableSchedule.blockLength raw.1.length) raw

theorem rankInput_polyT : PolyT rankInput := by
  have hm := RankDA.orderRows_polyT
  have hc := RankDA.irreducibleCodes_polyT
  have hr := PolyT.range (Unary.of_length hc)
  have hs := ScheduleComplexity.blockLength_polyT
    (Unary.of_length (PolyT.id' (α := RankDA.Input)).fst)
  have hn : PolyT (fun raw : RankDA.Input => raw.1.length) := by fun_prop
  change PolyT (fun raw : RankDA.Input =>
    (RankDA.orderRows raw, raw.1.length * ExecutableSchedule.blockLength raw.1.length,
      List.range (RankDA.irreducibleCodes raw).length))
  exact PolyT.prodMk hm (PolyT.prodMk (PolyT.mul hn hs) hr)

def input (code : List Bool) : RawTraversal.Input := rankInput (RankInputCode.decode code)

theorem input_polyT : PolyT input := rankInput_polyT.comp RankInputCode.decode_polyT

def machine : Stepped (List Bool) (List (List Nat)) :=
  Stepped.mapIn input RawTraversal.machine

@[instance_reducible] def machine_isPolyT : IsPolyT machine := by
  letI := RawTraversal.machine_isPolyT
  exact IsPolyT.mapIn input_polyT

def time (p : RankInput) : Nat :=
  RawBranching.nodes (RankTraversal.tree p (ExecutableSchedule.blockLength p.men.length))

def leaves (p : RankInput) : List (List Nat) :=
  (RankTraversal.tree p (ExecutableSchedule.blockLength p.men.length)).leaves.map (List.map Fin.val)

set_option maxHeartbeats 2000000 in
theorem machine_runs_polynomial_size :
    ∃ q : Nat → Nat, PB q ∧ Monotone q ∧ ∀ (p : RankInput) (width : Nat),
      (∀ row ∈ p.men ++ p.women, ∀ a ∈ row, a < 2 ^ width) →
      machine.Runs (RankInputCode.encode p width) (time p)
        ((time p + 2) * (q (RankInputCode.encode p width).length + 2)) (leaves p) := by
  obtain ⟨q, hq, hm, hlen⟩ := PolyT.len_bound input_polyT
  let r : Nat → Nat := fun n => q (3 * n + 2)
  have hr : PB r := hq.comp (((PB.const 3).mul PB.id').add (PB.const 2))
  have hrm : Monotone r := fun _ _ h => hm (by omega)
  refine ⟨r, hr, hrm, ?_⟩
  intro p width hb
  let D := ExecutableSchedule.blockLength p.men.length
  have he : input (RankInputCode.encode p width) = RankTraversal.input D (p.men, p.women) := by
    unfold input rankInput
    rw [RankInputCode.decode_encode p width hb]
  have ht := RawTraversal.machine_runs (RankDA.orderRows (p.men, p.women)) (p.men.length * D)
    (List.range (RankDA.irreducibleCodes (p.men, p.women)).length)
  rw [RankTraversal.tree_correct, RawBranching.mapTree_leaves, RawBranching.mapTree_nodes] at ht
  have hs := RankTraversal.state_bound_le_word (input (RankInputCode.encode p width)) (time p)
  rw [he] at hs
  have hl := hlen (RankInputCode.encode p width)
  rw [len_bools] at hl
  rw [he] at hl
  have hstate := hs.trans (Nat.mul_le_mul_left (time p + 2) (Nat.add_le_add_right hl 2))
  have hrun : RawTraversal.machine.Runs (input (RankInputCode.encode p width)) (time p)
      ((time p + 2) * (r (RankInputCode.encode p width).length + 2)) (leaves p) := by
    rw [he]
    exact ht.mono le_rfl hstate
  exact Stepped.mapIn_runs hrun

theorem time_bound (p : RankInput) (hn : 0 < p.men.length) :
    time p < 2 ^ (3 + 8 * p.men.length / ExecutableSchedule.blockLength p.men.length) :=
  RankTraversal.nodes_bound p _ hn (ExecutableSchedule.blockLength_pos _)

end StableMatching.UniformTraversal

#print axioms StableMatching.UniformTraversal.machine_isPolyT
#print axioms StableMatching.UniformTraversal.machine_runs_polynomial_size
#print axioms StableMatching.UniformTraversal.time_bound
