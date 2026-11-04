import StableMatching.ParticipantBounds
import StableMatching.AnthropicBridge
import StableMatching.CountingRates

/-!
# Participant-subexponential exact-counting reduction

The count identity and numerical query budget are unconditional. The machine
application is factored through the original machine proposition so that the
final import can supply its actual proof. The budget counts SAT-machine steps;
it does not by itself assert a Turing implementation of the matching compiler.
-/

namespace StableMatching.SubexponentialReduction

open MathEconLib.Matching

/-- The explicit DA/branching construction has a subexponential total SAT
budget, uniformly over all balanced markets with n participants on each side. -/
theorem reduction_budget (C : Nat) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : Nat, 0 < D ∧ ∃ a : Nat, ∀ n : Nat, 1 ≤ n →
      ∀ mkt : MarriageMarket (Fin n) (Fin n),
        (((StoppedCounting.reduce mkt (n * D)).map (fun φ =>
          MainResults.numSat φ.prepare.clauses)).sum = Nat.card mkt.StableMatching) ∧
        ((StoppedCounting.reduce mkt (n * D)).map (fun φ =>
          (MainResults.timeMin C 2 φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
            (a : ℝ) * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨D, hD, a, ha⟩ := CountingRates.oracle_list_budget C hε
  refine ⟨D, hD, a, ?_⟩
  intro n hn mkt
  constructor
  · have heq :
        (StoppedCounting.reduce mkt (n * D)).map (fun φ =>
          MainResults.numSat φ.prepare.clauses) =
        (StoppedCounting.reduce mkt (n * D)).map CNF.satCount := by
      apply List.map_congr_left
      intro φ _
      rw [← CNF.satCount_eq_anthropic_numSat, CNF.satCount_prepare]
    rw [heq]
    exact StoppedCounting.reduce_correct mkt (n * D)
  · exact ha n hn _
      (StoppedCounting.reduce_participant_query_bound mkt D (by omega) (by omega) hD)
      (StoppedCounting.reduce_variable_bound mkt (n * D))

/-- Application to the original SAT machine specification. The final theorem
supplies `hMain` by importing Anthropic's actual `Solution` proof. -/
theorem counting_machine_of_main (hMain : MainResults.MainTheorem) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : Nat),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ D : Nat, 0 < D ∧ ∃ a : Nat,
        ∀ n : Nat, 1 ≤ n → ∀ mkt : MarriageMarket (Fin n) (Fin n),
          (((StoppedCounting.reduce mkt (n * D)).map (fun φ =>
            MainResults.numSat φ.prepare.clauses)).sum = Nat.card mkt.StableMatching) ∧
          (∀ φ ∈ StoppedCounting.reduce mkt (n * D),
            MainResults.CountsWithin M 2 φ.prepare.clauses
              (MainResults.timeMin C 2 φ.prepare.clauses.length φ.prepare.numVars)) ∧
          ((StoppedCounting.reduce mkt (n * D)).map (fun φ =>
            (MainResults.timeMin C 2 φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
              (a : ℝ) * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨M, C, hfinite, hmachine⟩ := anthropic_prepared_machine hMain
  refine ⟨M, C, hfinite, ?_⟩
  intro ε hε
  obtain ⟨D, hD, a, ha⟩ := reduction_budget C hε
  refine ⟨D, hD, a, ?_⟩
  intro n hn mkt
  obtain ⟨hcount, hbudget⟩ := ha n hn mkt
  refine ⟨hcount, ?_, hbudget⟩
  intro φ hφ
  simpa only [max_self] using
    (hmachine 2 φ (StoppedCounting.reduce_width mkt (n * D) φ hφ)).1

end StableMatching.SubexponentialReduction
