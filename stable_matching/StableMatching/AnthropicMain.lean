import Solution
import StableMatching.CompactSubexponential
import StableMatching.UniformCounting

/-!
# The compact matching reduction applied to Anthropic's actual proof

This entry point imports `Solution`, rather than accepting its conclusion as
a hypothesis. The reduction and its count correspondence are constructed
from the existing MathEconLib marriage market.

The bound is on the SAT-machine queries plus any fixed polynomial expression
per query. It does not assert an additional Turing implementation or cost
theorem for the matching compiler.
-/

namespace StableMatching

open MathEconLib.Matching

/-- One executable integer schedule, exact counts, and a fourth-root-logarithm
bound on the sum of all original-machine query times. -/
theorem uniform_logarithmic_queries :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : Nat),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ n : Nat, 1 ≤ n → ∀ mkt : MarriageMarket (Fin n) (Fin n),
        (((UniformCounting.queries mkt).map (fun φ =>
          MainResults.numSat φ.prepare.clauses)).sum = Nat.card mkt.StableMatching) ∧
        (∀ φ ∈ UniformCounting.queries mkt,
          MainResults.CountsWithin M (UniformCounting.width n) φ.prepare.clauses
            (MainResults.timeMin C (UniformCounting.width n)
              φ.prepare.clauses.length φ.prepare.numVars)) ∧
        ((UniformCounting.queries mkt).map (fun φ =>
          (MainResults.timeMin C (UniformCounting.width n)
            φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
          (2 : ℝ) ^
            (((32 + 816 * 65 ^ 3 * C : Nat) : ℝ) * (n : ℝ) /
              (MainTheoremForms.lg ((n : ℝ) + 4)) ^ (1 / 4 : ℝ)) :=
  UniformCounting.counting_machine_of_main MainResults.mainTheorem

theorem participant_subexponential_queries :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : Nat),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (p : Nat) (ε : ℝ), 0 < ε →
        ∃ (D ℓ : Nat) (hD : 0 < D), 0 < ℓ ∧ D + 1 ≤ 2 ^ ℓ ∧
          ∃ a : Nat, ∀ n : Nat, 1 ≤ n →
            ∀ mkt : MarriageMarket (Fin n) (Fin n),
              (((CompactReduction.reduce mkt D hD ℓ).map (fun φ =>
                MainResults.numSat φ.prepare.clauses)).sum = Nat.card mkt.StableMatching) ∧
              (∀ φ ∈ CompactReduction.reduce mkt D hD ℓ,
                MainResults.CountsWithin M (max (2 * ℓ) 2) φ.prepare.clauses
                  (MainResults.timeMin C (max (2 * ℓ) 2)
                    φ.prepare.clauses.length φ.prepare.numVars)) ∧
              (((CompactReduction.reduce mkt D hD ℓ).map (fun φ =>
                (MainResults.timeMin C (max (2 * ℓ) 2)
                  φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum +
                ((n : ℝ) + 2) ^ p *
                  (((CompactReduction.reduce mkt D hD ℓ).length : ℝ) + 1) ≤
                (a : ℝ) * (2 : ℝ) ^ (ε * n)) :=
  CompactSubexponential.counting_machine_of_main MainResults.mainTheorem

end StableMatching

#print axioms MainResults.mainTheorem
#print axioms StableMatching.uniform_logarithmic_queries
#print axioms StableMatching.participant_subexponential_queries
