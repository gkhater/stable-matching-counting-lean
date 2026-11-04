/-
Copyright (c) 2026 MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MathEconLib contributors
-/
import StableMatching.MarketRuntime

/-! Counting-machine extension of MathEconLib's existing marriage market.

Import this module for the public result. The pure marriage library retains
its existing dependencies; the external SAT proof is supplied by this package.
-/

namespace MathEconLib.Matching.MarriageMarket

/-- One fixed finite-alphabet Turing machine counts the stable matchings of
every balanced market, from its normalized preference-rank bit string, below
every positive participant-exponential rate. Reading, constructing and
simulating the entire algorithm are included in the time bound. -/
theorem subexponential_exact_counting :
    ∃ N : Turing.TM2ComputableAux Bool Bool,
      (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ c : Nat, ∀ {n : Nat}
        (mkt : MathEconLib.Matching.MarriageMarket (Fin n) (Fin n)), 1 ≤ n →
        ∃ T : Nat,
          Wrap.Outputs N
            (StableMatching.RankInputCode.encode (rankRepresentation mkt) (n + 1))
            (Nat.bits (Nat.card mkt.StableMatching)) T ∧
          (T : ℝ) ≤ (c : ℝ) * (2 : ℝ) ^ (ε * n) :=
  StableMatching.MarketRuntime.exists_market_subexponential_counter

end MathEconLib.Matching.MarriageMarket

#print axioms MathEconLib.Matching.MarriageMarket.subexponential_exact_counting
