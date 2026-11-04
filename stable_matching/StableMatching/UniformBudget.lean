import StableMatching.UniformTraversal
import StableMatching.UniformCounting
import StableMatching.HostBudget

/-! One budget pays for the input, actual branching nodes and actual SAT runs. -/

namespace StableMatching.UniformBudget

open MathEconLib.Matching.MarriageMarket

noncomputable def satTime (C : Nat) (p : RankInput) : Nat :=
  ((UniformCounting.queries p.market).map (fun phi => MainResults.timeMin C
    (UniformCounting.width p.men.length) phi.prepare.clauses.length phi.prepare.numVars)).sum

noncomputable def budget (C : Nat) (p : RankInput) (width : Nat) : Nat :=
  (RankInputCode.encode p width).length + UniformTraversal.time p + satTime C p + 1

noncomputable def exponent (C n : Nat) : ℝ :=
  ((48 + 816 * 65 ^ 3 * C : Nat) : ℝ) * (n : ℝ) / LogarithmicRate.rootScale n

theorem exponent_nonneg (C n : Nat) : 0 ≤ exponent C n := by
  unfold exponent
  have := LogarithmicRate.rootScale_ge_one n
  positivity

private theorem cast_list_sum (xs : List Nat) :
    ((xs.sum : Nat) : ℝ) = (xs.map (fun x : Nat => (x : ℝ))).sum := by
  induction xs <;> simp_all

theorem satTime_bound (C : Nat) (p : RankInput) (hn : 1 ≤ p.men.length) :
    (satTime C p : ℝ) ≤ (2 : ℝ) ^ exponent C p.men.length := by
  have h := UniformCounting.query_budget p.market C hn
  have hc : (satTime C p : ℝ) = ((UniformCounting.queries p.market).map (fun phi =>
      (MainResults.timeMin C (UniformCounting.width p.men.length)
        phi.prepare.clauses.length phi.prepare.numVars : ℝ))).sum := by
    unfold satTime
    rw [cast_list_sum]
    simp only [List.map_map, Function.comp_def]
  rw [hc]
  apply h.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  change ((32 + 816 * 65 ^ 3 * C : Nat) : ℝ) * (p.men.length : ℝ) /
    LogarithmicRate.rootScale p.men.length ≤ _
  unfold exponent
  have hr : 0 ≤ LogarithmicRate.rootScale p.men.length := by
    linarith [LogarithmicRate.rootScale_ge_one p.men.length]
  gcongr <;> norm_num

theorem traversal_bound (C : Nat) (p : RankInput) (hn : 1 ≤ p.men.length) :
    (UniformTraversal.time p : ℝ) ≤ (2 : ℝ) ^ exponent C p.men.length := by
  have ht := (UniformTraversal.time_bound p hn).le
  have hnat : (UniformTraversal.time p : ℝ) ≤
      (2 : ℝ) ^ (3 + 8 * p.men.length / ExecutableSchedule.blockLength p.men.length : Nat) := by
    exact_mod_cast ht
  apply hnat.trans
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [ExecutableSchedule.blockLength_eq]
  have hb := LogarithmicRate.branch_exponent_le p.men.length
  have htwo := LogarithmicRate.two_le_inverse_root p.men.length hn
  let r : ℝ := (p.men.length : ℝ) / LogarithmicRate.rootScale p.men.length
  have hr : 0 ≤ r := by
    have := LogarithmicRate.rootScale_ge_one p.men.length
    dsimp [r]
    positivity
  have hb' : ((3 + 8 * p.men.length / LogarithmicRate.blockLength p.men.length : Nat) : ℝ) ≤
      3 + 16 * r := by
    dsimp [r]
    rw [← mul_div_assoc]
    push_cast at hb ⊢
    linarith
  have ht' : 2 ≤ 16 * r := by simpa only [r, mul_div_assoc] using htwo
  have he : exponent C p.men.length = 48 * r + (816 * 65 ^ 3 * C : Nat) * r := by
    unfold exponent r
    push_cast
    ring
  rw [he]
  have hrest : 0 ≤ ((816 * 65 ^ 3 * C : Nat) : ℝ) * r := mul_nonneg (Nat.cast_nonneg _) hr
  have hmiddle : 3 + 16 * r ≤ 48 * r := by linarith only [ht']
  exact (hb'.trans hmiddle).trans (le_add_of_nonneg_right hrest)

theorem budget_bound (C : Nat) (p : RankInput) (width : Nat) (hn : 1 ≤ p.men.length) :
    (budget C p width : ℝ) ≤ ((RankInputCode.encode p width).length + (3 : ℝ)) *
      (2 : ℝ) ^ exponent C p.men.length := by
  have ht := traversal_bound C p hn
  have hs := satTime_bound C p hn
  have he := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (exponent_nonneg C p.men.length)
  unfold budget
  push_cast
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (RankInputCode.encode p width).length by positivity)
    (show 0 ≤ (2 : ℝ) ^ exponent C p.men.length - 1 by linarith)]

theorem polynomial_budget_bound {f : Nat → Nat} (hf : Groundwork.PB f) :
    ∃ a : Nat, ∀ (C : Nat) (p : RankInput) (width : Nat), 1 ≤ p.men.length →
      (f (budget C p width) : ℝ) ≤ (a : ℝ) * ((RankInputCode.encode p width).length + (4 : ℝ)) ^ a *
        (2 : ℝ) ^ ((a : ℝ) * exponent C p.men.length) := by
  obtain ⟨a, ha⟩ := HostBudget.polynomial_exponential_budget hf
  exact ⟨a, fun C p width hn => ha _ _ _ (exponent_nonneg _ _) (budget_bound C p width hn)⟩

end StableMatching.UniformBudget
