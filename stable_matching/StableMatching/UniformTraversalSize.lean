import StableMatching.UniformTraversal
import StableMatching.MachineOutputSize

/-! All traversal states and any costed next stage are polynomial in the
input length plus the proved number of visited tree nodes. -/

namespace StableMatching.UniformTraversalSize

open Groundwork MathEconLib.Matching.MarriageMarket

theorem machine_runs_budget :
    ∃ q : Nat → Nat, PB q ∧ Monotone q ∧ ∀ (p : RankInput) (width : Nat),
      (∀ row ∈ p.men ++ p.women, ∀ a ∈ row, a < 2 ^ width) →
      UniformTraversal.machine.Runs (RankInputCode.encode p width) (UniformTraversal.time p)
        (q ((RankInputCode.encode p width).length + UniformTraversal.time p))
        (UniformTraversal.leaves p) := by
  obtain ⟨q, hq, hm, hruns⟩ := UniformTraversal.machine_runs_polynomial_size
  let r : Nat → Nat := fun n => (n + 2) * (q n + 2)
  have hr : PB r := (PB.id'.add (PB.const 2)).mul (hq.add (PB.const 2))
  have hrm : Monotone r := by
    intro a b hab
    exact Nat.mul_le_mul (by omega) (by have := hm hab; omega)
  refine ⟨r, hr, hrm, ?_⟩
  intro p width hb
  apply (hruns p width hb).mono le_rfl
  exact Nat.mul_le_mul (by omega) (Nat.add_le_add_right (hm (by omega)) 2)

theorem after_length_bound {C : Type} [Enc C]
    (f : List Bool × List (List Nat) → C) (hf : PolyT f) :
    ∃ q : Nat → Nat, PB q ∧ Monotone q ∧ ∀ (p : RankInput) (width : Nat),
      (∀ row ∈ p.men ++ p.women, ∀ a ∈ row, a < 2 ^ width) →
      len (f (RankInputCode.encode p width, UniformTraversal.leaves p)) ≤
        q ((RankInputCode.encode p width).length + UniformTraversal.time p) := by
  letI := UniformTraversal.machine_isPolyT
  obtain ⟨r, hr, hrm, hruns⟩ := machine_runs_budget
  obtain ⟨q, hq, hqm, hlen⟩ :=
    MachineOutputSize.after_length_bound UniformTraversal.machine f hf
  let s : Nat → Nat := fun n => q (3 * n + 2 + r n)
  have hs : PB s := hq.comp ((((PB.const 3).mul PB.id').add (PB.const 2)).add hr)
  have hsm : Monotone s := by
    intro a b hab
    exact hqm (by have := hrm hab; omega)
  refine ⟨s, hs, hsm, ?_⟩
  intro p width hb
  have h := hlen _ _ _ _ (hruns p width hb)
  rw [len_bools] at h
  exact h.trans (hqm (by omega))

end StableMatching.UniformTraversalSize
