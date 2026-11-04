import StableMatching.UniformTraversal
import CountKSat.Host

/-! Genuine machine compilation of the traversal, query construction and counting loop.
The reusable lemma below charges both computation stages and the original input
kept between them; its concrete query constructor and loop are instantiated by
the matching compiler. -/

namespace StableMatching.MachineComposition

open Groundwork Turing

abbrev QueryWords := List (List Bool)
abbrev QueryInput := List Bool × List (List Nat)

def program (queries : QueryInput → QueryWords) (counter : Stepped QueryWords Nat) :
    Stepped (List Bool) (List Bool) :=
  Stepped.mapOut
    (Stepped.bind UniformTraversal.machine (Stepped.mapIn queries counter)) Nat.bits

@[instance_reducible] def program_isPolyT
    (queries : QueryInput → QueryWords) (counter : Stepped QueryWords Nat)
    (hq : PolyT queries) [IsPolyT counter] : IsPolyT (program queries counter) := by
  letI := UniformTraversal.machine_isPolyT
  letI := IsPolyT.mapIn (M := counter) hq
  letI := IsPolyT.bind (M := UniformTraversal.machine) (N := Stepped.mapIn queries counter)
  exact IsPolyT.mapOut (by fun_prop)

/-- One fixed multi-stack machine implements both stages. Its polynomial
overhead is fixed before the input, branch parameters and any run bounds. -/
theorem exists_machine (queries : QueryInput → QueryWords) (counter : Stepped QueryWords Nat)
    (hq : PolyT queries) [IsPolyT counter] :
    ∃ (N : TM2ComputableAux Bool Bool) (q : Nat), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (leaves : List (List Nat)) (answer t₁ S₁ t₂ S₂ : Nat),
        UniformTraversal.machine.Runs x t₁ S₁ leaves →
        counter.Runs (queries (x, leaves)) t₂ S₂ answer →
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun)
          (some ((Nat.bits answer).map N.outputAlphabet.invFun))
          (q * (t₁ + 1 + t₂ + 1) * (x.length + (max (size x + S₁) S₂ + 1) + 1) ^ q)) := by
  letI := program_isPolyT queries counter hq
  obtain ⟨N, q, hfinite, hrun⟩ := CountKSat.exists_tmW (program queries counter)
  refine ⟨N, q, hfinite, ?_⟩
  intro x leaves answer t₁ S₁ t₂ S₂ hfirst hsecond
  have hbody : (Stepped.mapIn queries counter).Runs (x, leaves) t₂ S₂ answer :=
    Stepped.mapIn_runs hsecond
  have hboth := Stepped.bind_runs hfirst hbody
  exact hrun x _ _ _ (Stepped.mapOut_runs hboth)

end StableMatching.MachineComposition
