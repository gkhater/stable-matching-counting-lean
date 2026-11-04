import StableMatching.CompactReduction
import StableMatching.CompactRates
import StableMatching.AnthropicBridge

/-!
# Exact compact matching queries with a participant-subexponential budget

All formulas are constructed from the market, including the chain partitions.
The last bound absorbs any fixed polynomial overhead per query. It counts the
SAT machine's steps plus that polynomial expression; a separate implementation
cost proof is needed to identify it with all matching-compiler machine steps.
-/

namespace StableMatching.CompactSubexponential

open MathEconLib.Matching

theorem prepared_count_correct {m n : Nat}
    (mkt : MarriageMarket (Fin m) (Fin n))
    (D : Nat) (hD : 0 < D) (ℓ : Nat) (hcap : D + 1 ≤ 2 ^ ℓ) :
    ((CompactReduction.reduce mkt D hD ℓ).map (fun φ =>
      MainResults.numSat φ.prepare.clauses)).sum = Nat.card mkt.StableMatching := by
  have heq : (CompactReduction.reduce mkt D hD ℓ).map (fun φ =>
        MainResults.numSat φ.prepare.clauses) =
      (CompactReduction.reduce mkt D hD ℓ).map CNF.satCount := by
    apply List.map_congr_left
    intro φ _
    rw [← CNF.satCount_eq_anthropic_numSat, CNF.satCount_prepare]
  rw [heq]
  exact CompactReduction.reduce_correct mkt D hD ℓ hcap

/-- The same machine and constant serve every market, accuracy parameter and
fixed polynomial overhead. Only the reduction's block and bit sizes depend
on the requested exponential rate. -/
theorem counting_machine_of_main (hMain : MainResults.MainTheorem) :
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
                (a : ℝ) * (2 : ℝ) ^ (ε * n)) := by
  obtain ⟨M, C, hfinite, hmachine⟩ := anthropic_prepared_machine hMain
  refine ⟨M, C, hfinite, ?_⟩
  intro p ε hε
  obtain ⟨D, ℓ, hD, _hℓeq, hℓ, hcap, a, b, hab⟩ :=
    CompactRates.oracle_and_overhead_budget C p hε
  refine ⟨D, ℓ, hD, hℓ, hcap, a + b, ?_⟩
  intro n hn mkt
  have hlen := CompactReduction.reduce_query_bound mkt D hD ℓ (by omega) (by omega)
  have hvars := CompactReduction.reduce_variable_bound mkt D hD ℓ
  obtain ⟨hquery, hoverhead⟩ := hab n hn _ hlen hvars
  refine ⟨prepared_count_correct mkt D hD ℓ hcap, ?_, ?_⟩
  · intro φ hφ
    exact (hmachine (2 * ℓ) φ (CompactReduction.reduce_width mkt D hD ℓ φ hφ)).1
  · push_cast
    nlinarith

end StableMatching.CompactSubexponential
