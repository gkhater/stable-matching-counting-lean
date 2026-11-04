import StableMatching.LogarithmicRate
import StableMatching.CompactSubexponential

/-! The explicit fourth-root-logarithm budget applied to the actual matching
formulas. Executable integer scheduling is supplied separately. -/

namespace StableMatching.LogarithmicCounting

open MathEconLib.Matching
open LogarithmicRate

theorem query_budget {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (C : Nat) (hn : 1 ≤ n) :
    ((CompactReduction.reduce mkt (blockLength n) (blockLength_pos n) (bitWidth n)).map
      (fun φ => (MainResults.timeMin C (max (2 * bitWidth n) 2)
        φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
      (2 : ℝ) ^
        (((32 + 816 * 65 ^ 3 * C : Nat) : ℝ) * (n : ℝ) /
          (MainTheoremForms.lg ((n : ℝ) + 4)) ^ (1 / 4 : ℝ)) :=
  (RateTradeoff.compact_query_budget mkt C (blockLength n) (blockLength_pos n)
    (bitWidth n) (by omega)).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (exponent_le C n hn))

theorem count_correct {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n)) :
    ((CompactReduction.reduce mkt (blockLength n) (blockLength_pos n) (bitWidth n)).map
      (fun φ => MainResults.numSat φ.prepare.clauses)).sum = Nat.card mkt.StableMatching :=
  CompactSubexponential.prepared_count_correct mkt (blockLength n) (blockLength_pos n)
    (bitWidth n) (bitWidth_capacity n)

theorem counting_machine_of_main (hMain : MainResults.MainTheorem) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : Nat),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ n : Nat, 1 ≤ n → ∀ mkt : MarriageMarket (Fin n) (Fin n),
        (((CompactReduction.reduce mkt (blockLength n) (blockLength_pos n) (bitWidth n)).map
          (fun φ => MainResults.numSat φ.prepare.clauses)).sum = Nat.card mkt.StableMatching) ∧
        (∀ φ ∈ CompactReduction.reduce mkt (blockLength n) (blockLength_pos n) (bitWidth n),
          MainResults.CountsWithin M (max (2 * bitWidth n) 2) φ.prepare.clauses
            (MainResults.timeMin C (max (2 * bitWidth n) 2)
              φ.prepare.clauses.length φ.prepare.numVars)) ∧
        ((CompactReduction.reduce mkt (blockLength n) (blockLength_pos n) (bitWidth n)).map
          (fun φ => (MainResults.timeMin C (max (2 * bitWidth n) 2)
            φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
          (2 : ℝ) ^
            (((32 + 816 * 65 ^ 3 * C : Nat) : ℝ) * (n : ℝ) /
              (MainTheoremForms.lg ((n : ℝ) + 4)) ^ (1 / 4 : ℝ)) := by
  obtain ⟨M, C, hfinite, hmachine⟩ := anthropic_prepared_machine hMain
  refine ⟨M, C, hfinite, ?_⟩
  intro n hn mkt
  refine ⟨count_correct mkt, ?_, query_budget mkt C hn⟩
  intro φ hφ
  exact (hmachine (2 * bitWidth n) φ
    (CompactReduction.reduce_width mkt (blockLength n) (blockLength_pos n)
      (bitWidth n) φ hφ)).1

end StableMatching.LogarithmicCounting
