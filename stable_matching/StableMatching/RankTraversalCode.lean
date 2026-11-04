import StableMatching.RankTraversal
import StableMatching.RankInputCode

/-! The actual branching traversal, started from a Boolean rank-table code. -/

namespace StableMatching.RankTraversalCode

open Groundwork MathEconLib.Matching.MarriageMarket

def machine (D : Nat) : Stepped (List Bool) (List (List Nat)) :=
  Stepped.mapIn RankInputCode.decode (RankTraversal.machine D)

@[instance_reducible] def machine_isPolyT (D : Nat) : IsPolyT (machine D) := by
  letI := RankTraversal.machine_isPolyT D
  exact IsPolyT.mapIn RankInputCode.decode_polyT

theorem machine_runs_polynomial_size (D : Nat) :
    ∃ q : Nat → Nat, PB q ∧ Monotone q ∧ ∀ (p : RankInput) (width : Nat),
      (∀ row ∈ p.men ++ p.women, ∀ a ∈ row, a < 2 ^ width) →
      (machine D).Runs (RankInputCode.encode p width)
        (RawBranching.nodes (RankTraversal.tree p D))
        ((RawBranching.nodes (RankTraversal.tree p D) + 2) *
          (q (RankInputCode.encode p width).length + 2))
        ((RankTraversal.tree p D).leaves.map (List.map Fin.val)) := by
  obtain ⟨q, hq, hm, hruns⟩ := RankTraversal.machine_runs_polynomial_size D
  obtain ⟨r, hr, hrm, hrlen⟩ := PolyT.len_bound RankInputCode.decode_polyT
  let s : Nat → Nat := fun n => q (r (3 * n + 2))
  have hs : PB s := hq.comp (hr.comp (((PB.const 3).mul PB.id').add (PB.const 2)))
  have hsm : Monotone s := by
    intro a b hab
    exact hm (hrm (by omega))
  refine ⟨s, hs, hsm, ?_⟩
  intro p width hb
  have hdecode := RankInputCode.decode_encode p width hb
  have hlength : len (p.men, p.women) ≤ r (3 * (RankInputCode.encode p width).length + 2) := by
    simpa only [hdecode, len_bools] using hrlen (RankInputCode.encode p width)
  have hstate := Nat.mul_le_mul_left (RawBranching.nodes (RankTraversal.tree p D) + 2)
    (Nat.add_le_add_right (hm hlength) 2)
  have h := (hruns p).mono le_rfl hstate
  have hh : (RankTraversal.machine D).Runs (RankInputCode.decode (RankInputCode.encode p width))
      (RawBranching.nodes (RankTraversal.tree p D))
      ((RawBranching.nodes (RankTraversal.tree p D) + 2) *
        (s (RankInputCode.encode p width).length + 2))
      ((RankTraversal.tree p D).leaves.map (List.map Fin.val)) := by
    simpa only [hdecode] using h
  exact Stepped.mapIn_runs hh

theorem machine_time_bound (p : RankInput) (D : Nat)
    (hn : 0 < p.men.length) (hD : 0 < D) :
    RawBranching.nodes (RankTraversal.tree p D) < 2 ^ (3 + 8 * p.men.length / D) :=
  RankTraversal.nodes_bound p D hn hD

end StableMatching.RankTraversalCode

#print axioms StableMatching.RankTraversalCode.machine_isPolyT
#print axioms StableMatching.RankTraversalCode.machine_runs_polynomial_size
