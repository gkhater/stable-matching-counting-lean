import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Filter

namespace StableMatching

/-- Boolean CNF with in-range variable indices and explicit literal polarity. -/
structure CNF where
  numVars : ℕ
  clauses : List (List (Fin numVars × Bool))

def CNF.IsThreeCNF (φ : CNF) : Prop :=
  ∀ clause ∈ φ.clauses, clause.length ≤ 3

def CNF.Satisfies (φ : CNF) (assignment : Fin φ.numVars → Bool) : Prop :=
  ∀ clause ∈ φ.clauses,
    ∃ literal ∈ clause, assignment literal.1 = literal.2

noncomputable def CNF.satCount (φ : CNF) : ℕ := by
  classical
  exact (Finset.univ.filter fun a : Fin φ.numVars → Bool => φ.Satisfies a).card

end StableMatching
