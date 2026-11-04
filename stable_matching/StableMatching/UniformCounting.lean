import StableMatching.ExecutableSchedule
import StableMatching.LogarithmicCounting

/-!
# A uniform executable matching-to-counting reduction

The parameter schedule uses integer logarithms and square roots only.
Its formulas preserve the exact stable-matching count. The explicit bound
is on the sum of the original SAT machine's query times; a cost theorem
for implementing the entire matching compiler as a Turing machine is separate.
-/

namespace StableMatching.UniformCounting

open MathEconLib.Matching

/-- The actual formulas, with no numerical tuning supplied by the caller. -/
def queries {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n)) : List CNF :=
  CompactReduction.reduce mkt (ExecutableSchedule.blockLength n)
    (ExecutableSchedule.blockLength_pos n) (ExecutableSchedule.bitWidth n)

def width (n : Nat) : Nat := max (2 * ExecutableSchedule.bitWidth n) 2

theorem count_correct {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n)) :
    ((queries mkt).map (fun φ => MainResults.numSat φ.prepare.clauses)).sum =
      Nat.card mkt.StableMatching :=
  CompactSubexponential.prepared_count_correct mkt (ExecutableSchedule.blockLength n)
    (ExecutableSchedule.blockLength_pos n) (ExecutableSchedule.bitWidth n)
      (ExecutableSchedule.bitWidth_capacity n)

theorem query_budget {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (C : Nat) (hn : 1 ≤ n) :
    ((queries mkt).map (fun φ => (MainResults.timeMin C (width n)
      φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
        (2 : ℝ) ^
          (((32 + 816 * 65 ^ 3 * C : Nat) : ℝ) * (n : ℝ) /
            (MainTheoremForms.lg ((n : ℝ) + 4)) ^ (1 / 4 : ℝ)) := by
  simpa only [queries, width, ExecutableSchedule.blockLength_eq,
    ExecutableSchedule.bitWidth_eq] using LogarithmicCounting.query_budget mkt C hn

theorem counting_machine_of_main (hMain : MainResults.MainTheorem) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : Nat),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ n : Nat, 1 ≤ n → ∀ mkt : MarriageMarket (Fin n) (Fin n),
        (((queries mkt).map (fun φ => MainResults.numSat φ.prepare.clauses)).sum =
          Nat.card mkt.StableMatching) ∧
        (∀ φ ∈ queries mkt,
          MainResults.CountsWithin M (width n) φ.prepare.clauses
            (MainResults.timeMin C (width n)
              φ.prepare.clauses.length φ.prepare.numVars)) ∧
        ((queries mkt).map (fun φ => (MainResults.timeMin C (width n)
          φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
            (2 : ℝ) ^
              (((32 + 816 * 65 ^ 3 * C : Nat) : ℝ) * (n : ℝ) /
                (MainTheoremForms.lg ((n : ℝ) + 4)) ^ (1 / 4 : ℝ)) := by
  obtain ⟨M, C, hfinite, hmachine⟩ := anthropic_prepared_machine hMain
  refine ⟨M, C, hfinite, ?_⟩
  intro n hn mkt
  refine ⟨count_correct mkt, ?_, query_budget mkt C hn⟩
  intro φ hφ
  exact (hmachine (2 * ExecutableSchedule.bitWidth n) φ
    (CompactReduction.reduce_width mkt (ExecutableSchedule.blockLength n)
      (ExecutableSchedule.blockLength_pos n) (ExecutableSchedule.bitWidth n) φ hφ)).1

end StableMatching.UniformCounting
