import StableMatching.UniformQueryWords
import StableMatching.UniformTraversalSize
import StableMatching.MachineComposition
import StableMatching.MachineCostBudget
import StableMatching.UniformBudget
import StableMatching.UniformRateLimit

/-! One actual finite-alphabet machine counts stable matchings, with the
costs of reading, DA, branching, encoding, SAT simulation and summation included. -/

namespace StableMatching.UniformRuntime

open Groundwork Turing MathEconLib.Matching.MarriageMarket

private theorem sum_map_succ {A : Type} (f : A → Nat) (xs : List A) :
    (xs.map (fun x => f x + 1)).sum = (xs.map f).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

theorem exists_machine_polynomial_budget :
    ∃ (N : TM2ComputableAux Bool Bool) (C : Nat) (r : Nat → Nat),
      (∀ k, Finite (N.tm.Γ k)) ∧ PB r ∧ ∀ (p : RankInput) (width : Nat),
        (∀ row ∈ p.men ++ p.women, ∀ a ∈ row, a < 2 ^ width) →
        Wrap.Outputs N (RankInputCode.encode p width)
          (Nat.bits (Nat.card p.market.StableMatching)) (r (UniformBudget.budget C p width)) := by
  obtain ⟨M, C, _, K, ⟨hpoly⟩, hcounter⟩ := SATFormulaFold.exists_prepared_sum_runs
  letI : IsPolyT (SATMachineFold.sumProgram K) := hpoly
  obtain ⟨space, hspace, hspaceMono, hfirst⟩ := UniformTraversalSize.machine_runs_budget
  obtain ⟨words, hwords, hwordsMono, hwordLen⟩ :=
    UniformTraversalSize.after_length_bound UniformQueryWords.queries UniformQueryWords.queries_polyT
  obtain ⟨N, q, hfinite, hhost⟩ := MachineComposition.exists_machine
    UniformQueryWords.queries (SATMachineFold.sumProgram K) UniformQueryWords.queries_polyT
  obtain ⟨r, hr, hcost⟩ := MachineCostBudget.host_cost_polynomial q K.a space words hspace hwords
  refine ⟨N, C, r, hfinite, hr, ?_⟩
  intro p width hb
  let code := RankInputCode.encode p width
  let L := code.length
  let Nnodes := UniformTraversal.time p
  let V := UniformBudget.satTime C p
  let B := UniformBudget.budget C p width
  let Q := (UniformCounting.queries p.market).length
  let W := size (SATFormulaFold.words p.market)
  let S := space (L + Nnodes)
  let U := W + (p.men.length * p.men.length + 2) + (K.a * (W + 1) + K.a * V) + 1
  have hL : L ≤ B := by dsimp [B, UniformBudget.budget, L, code]; omega
  have hN : Nnodes ≤ B := by dsimp [B, UniformBudget.budget, Nnodes]; omega
  have hV : V ≤ B := by dsimp [B, UniformBudget.budget, V]; omega
  have hLN : L + Nnodes ≤ B := by dsimp [B, UniformBudget.budget, L, code, Nnodes]; omega
  have hn : p.men.length ≤ B :=
    (MatchingAccumulatorBounds.market_size_le_encoded_input p width).trans hL
  have hQ : Q ≤ W := by
    have hh := EncodingBounds.length_le_size (SATFormulaFold.words p.market)
    simpa only [Q, W, SATFormulaFold.words, List.length_map] using hh
  have hW : W ≤ words B := by
    have hs := EncodingBounds.size_list_le_len
      (EncodingBounds.size_list_le_len EncodingBounds.size_bool_le_len) (SATFormulaFold.words p.market)
    have hh := hwordLen p width hb
    rw [UniformQueryWords.queries_eq p width hb] at hh
    exact hs.trans (hh.trans (hwordsMono hLN))
  have hS : S ≤ space B := hspaceMono hLN
  have hsecond : (SATMachineFold.sumProgram K).Runs
      (UniformQueryWords.queries (code, UniformTraversal.leaves p)) (V + Q) U
      (Nat.card p.market.StableMatching) := by
    rw [UniformQueryWords.queries_eq p width hb]
    apply (hcounter p.market).mono
    · change ((UniformCounting.queries p.market).map (fun phi =>
        MainResults.timeMin C (UniformCounting.width p.men.length)
          phi.prepare.clauses.length phi.prepare.numVars + 1)).sum ≤ _
      rw [sum_map_succ]
      exact le_rfl
    · change W + ((p.men.length * p.men.length + 2) + (K.a * (W + 1) + K.a * V)) + 1 ≤ U
      dsimp [U]
      omega
  have hrun := hhost code (UniformTraversal.leaves p) (Nat.card p.market.StableMatching)
    Nnodes S (V + Q) U (hfirst p width hb) hsecond
  apply Wrap.Outputs.mono hrun
  rw [EncodingBounds.size_bools]
  exact hcost B L Nnodes V p.men.length Q W S hL hN hV hn hQ hW hS

/-- All stages are charged to one multi-stack Turing machine. Its input is
an explicit rank-table bit string and its output is the binary exact count. -/
theorem exists_matching_counter :
    ∃ (N : TM2ComputableAux Bool Bool) (a b : Nat),
      (∀ k, Finite (N.tm.Γ k)) ∧ ∀ (p : RankInput) (width : Nat),
        (∀ row ∈ p.men ++ p.women, ∀ v ∈ row, v < 2 ^ width) → 1 ≤ p.men.length →
        ∃ T : Nat, Wrap.Outputs N (RankInputCode.encode p width)
          (Nat.bits (Nat.card p.market.StableMatching)) T ∧
          (T : ℝ) ≤ (a : ℝ) * ((RankInputCode.encode p width).length + (4 : ℝ)) ^ a *
            (2 : ℝ) ^ ((b : ℝ) * p.men.length / LogarithmicRate.rootScale p.men.length) := by
  obtain ⟨N, C, r, hfinite, hr, hrun⟩ := exists_machine_polynomial_budget
  obtain ⟨a, ha⟩ := UniformBudget.polynomial_budget_bound hr
  refine ⟨N, a, a * (48 + 816 * 65 ^ 3 * C), hfinite, ?_⟩
  intro p width hb hn
  refine ⟨r (UniformBudget.budget C p width), hrun p width hb, ?_⟩
  have hh := ha C p width hn
  have he : (a : ℝ) * UniformBudget.exponent C p.men.length =
      ((a * (48 + 816 * 65 ^ 3 * C) : Nat) : ℝ) * p.men.length /
        LogarithmicRate.rootScale p.men.length := by
    unfold UniformBudget.exponent
    push_cast
    ring
  simpa only [he] using hh

/-- The same fixed counter works below every positive participant-exponential
rate; only the multiplicative bound changes with the requested rate. -/
theorem exists_subexponential_counter :
    ∃ (N : TM2ComputableAux Bool Bool) (a : Nat), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ c : Nat, ∀ (p : RankInput) (width : Nat),
        (∀ row ∈ p.men ++ p.women, ∀ v ∈ row, v < 2 ^ width) → 1 ≤ p.men.length →
        ∃ T : Nat, Wrap.Outputs N (RankInputCode.encode p width)
          (Nat.bits (Nat.card p.market.StableMatching)) T ∧
          (T : ℝ) ≤ (c : ℝ) * ((RankInputCode.encode p width).length + (4 : ℝ)) ^ a *
            (2 : ℝ) ^ (ε * p.men.length) := by
  obtain ⟨N, a, b, hfinite, hrun⟩ := exists_matching_counter
  refine ⟨N, a, hfinite, ?_⟩
  intro ε hε
  obtain ⟨c, hc⟩ := UniformRateLimit.exponent_below (A := (b : ℝ)) (Nat.cast_nonneg _) hε
  refine ⟨a * c, ?_⟩
  intro p width hb hn
  obtain ⟨T, hT, ht⟩ := hrun p width hb hn
  refine ⟨T, hT, ht.trans ?_⟩
  have hh := hc p.men.length hn
  calc
    _ ≤ (a : ℝ) * ((RankInputCode.encode p width).length + (4 : ℝ)) ^ a *
        ((c : ℝ) * (2 : ℝ) ^ (ε * p.men.length)) := by gcongr
    _ = _ := by push_cast; ring

end StableMatching.UniformRuntime

#print axioms StableMatching.UniformRuntime.exists_machine_polynomial_budget
#print axioms StableMatching.UniformRuntime.exists_matching_counter
#print axioms StableMatching.UniformRuntime.exists_subexponential_counter
