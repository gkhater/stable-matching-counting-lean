import StableMatching.AnthropicBridge
import Wrap.Arith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Numerical budget for a list of counting-oracle queries

The time bound of the imported SAT theorem depends on the number of variables
through `N * lg(lg N) / sqrt(lg N)`. The existing `Wrap.Arith.rate_below`
absorbs this factor into any positive exponential rate.
-/

namespace StableMatching.CountingRates

/-- The two-CNF SAT time is bounded by its variable-side exponential term. -/
theorem timeMin_two_le_rate (C m N : ℕ) :
    (MainResults.timeMin C 2 m N : ℝ) ≤
      (2 : ℝ) ^ ((4 * (C : ℝ)) *
        ((N : ℝ) * MainTheoremForms.lg (MainTheoremForms.lg N) /
          Real.sqrt (MainTheoremForms.lg N))) := by
  unfold MainResults.timeMin
  calc
    (↑⌊(2 : ℝ) ^ ((C : ℝ) *
        min (MainResults.expM 2 m) (MainResults.expN 2 N))⌋₊ : ℝ) ≤
        (2 : ℝ) ^ ((C : ℝ) *
          min (MainResults.expM 2 m) (MainResults.expN 2 N)) :=
      Nat.floor_le (by positivity)
    _ ≤ (2 : ℝ) ^ ((C : ℝ) * MainResults.expN 2 N) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg C))
    _ = (2 : ℝ) ^ ((4 * (C : ℝ)) *
          ((N : ℝ) * MainTheoremForms.lg (MainTheoremForms.lg N) /
            Real.sqrt (MainTheoremForms.lg N))) := by
      congr 1
      unfold MainResults.expN MainResults.lg MainTheoremForms.lg
      ring

/-- At a fixed positive rate, every prepared query with at most `n*D`
original variables has an exponential time bound in `n*D + 4`. -/
theorem prepared_query_le (C D : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℕ, ∀ (n : ℕ) (φ : StableMatching.CNF),
      φ.numVars ≤ n * D →
      (MainResults.timeMin C 2 φ.prepare.clauses.length φ.prepare.numVars : ℝ) ≤
        (c : ℝ) * (2 : ℝ) ^ (δ * ((n : ℝ) * D + 4)) := by
  obtain ⟨c, hc⟩ := Wrap.Arith.rate_below
    (B := 4 * (C : ℝ)) (ε := δ) (by positivity) hδ
  refine ⟨c, ?_⟩
  intro n φ hvars
  have hN4 : 4 ≤ φ.prepare.numVars := by simp
  have hN : (φ.prepare.numVars : ℝ) ≤ (n : ℝ) * D + 4 := by
    have hnat : φ.prepare.numVars ≤ n * D + 4 := by
      simpa only [StableMatching.CNF.prepare_numVars] using
        Nat.add_le_add_right hvars 4
    exact_mod_cast hnat
  calc
    (MainResults.timeMin C 2 φ.prepare.clauses.length φ.prepare.numVars : ℝ) ≤
        (2 : ℝ) ^ ((4 * (C : ℝ)) *
          ((φ.prepare.numVars : ℝ) *
            MainTheoremForms.lg (MainTheoremForms.lg φ.prepare.numVars) /
              Real.sqrt (MainTheoremForms.lg φ.prepare.numVars))) :=
      timeMin_two_le_rate C _ _
    _ ≤ (c : ℝ) * (2 : ℝ) ^ (δ * φ.prepare.numVars) :=
      hc _ hN4
    _ ≤ (c : ℝ) * (2 : ℝ) ^ (δ * ((n : ℝ) * D + 4)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg c)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_left hN hδ.le

/-- List summation converts a uniform real bound into a length factor. -/
private theorem sum_le_length_mul {α : Type*} (xs : List α) (f : α → ℝ) (K : ℝ)
    (h : ∀ x ∈ xs, f x ≤ K) :
    (xs.map f).sum ≤ (xs.length : ℝ) * K := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : f x ≤ K := h x (by simp)
    have hxs : ∀ y ∈ xs, f y ≤ K := by
      intro y hy
      exact h y (by simp [hy])
    have htail := ih hxs
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_mul, one_mul]
    linarith

/-- Choose a constant block length so the tree's `8n/D` exponent uses at most
one third of the requested exponential rate. -/
theorem exists_block_length {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, 0 < D ∧ 8 / (D : ℝ) ≤ ε / 3 := by
  obtain ⟨D, hD⟩ := exists_nat_gt (24 / ε)
  have hDreal : (0 : ℝ) < D := lt_trans (by positivity) hD
  have hDnat : 0 < D := by exact_mod_cast hDreal
  refine ⟨D, hDnat, ?_⟩
  have hmul : 24 < ε * (D : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hD
    nlinarith
  apply (div_le_iff₀ hDreal).mpr
  nlinarith

/-- The integer-division branch exponent is bounded by its real quotient. -/
theorem branch_exponent_le {D n : ℕ} {ε : ℝ}
    (hD : 8 / (D : ℝ) ≤ ε / 3) :
    ((2 + 8 * n / D : ℕ) : ℝ) ≤ 2 + ε / 3 * n := by
  have hquot : (((8 * n) / D : ℕ) : ℝ) ≤
      (8 * (n : ℝ)) / D := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_div_le (α := ℝ) (m := 8 * n) (n := D))
  have hscale := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  calc
    ((2 + 8 * n / D : ℕ) : ℝ) = 2 + (((8 * n) / D : ℕ) : ℝ) := by push_cast; ring
    _ ≤ 2 + (8 * (n : ℝ)) / D := add_le_add_right hquot _
    _ = 2 + (8 / (D : ℝ)) * n := by ring
    _ ≤ 2 + ε / 3 * n := add_le_add_right hscale _

/-- The total time for all prepared two-CNF queries is below any requested
positive exponential rate, provided the list and variable bounds hold. -/
theorem oracle_list_budget (C : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, 0 < D ∧ ∃ a : ℕ,
      ∀ (n : ℕ), 1 ≤ n → ∀ (formulas : List StableMatching.CNF),
        formulas.length ≤ 2 ^ (2 + 8 * n / D) →
        (∀ φ ∈ formulas, φ.numVars ≤ n * D) →
        (formulas.map (fun φ =>
          (MainResults.timeMin C 2 φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
          (a : ℝ) * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨D, hDpos, hDbranch⟩ := exists_block_length hε
  let δ : ℝ := ε / (3 * (D : ℝ))
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδD : δ * (D : ℝ) = ε / 3 := by
    dsimp [δ]
    field_simp
  obtain ⟨c, hc⟩ := prepared_query_le C D hδ
  obtain ⟨a, ha⟩ := exists_nat_ge
    ((c : ℝ) * (2 : ℝ) ^ (2 + 4 * δ))
  refine ⟨D, hDpos, a, ?_⟩
  intro n _hn formulas hlen hvars
  have hlenR : (formulas.length : ℝ) ≤
      (2 : ℝ) ^ (((2 + 8 * n / D : ℕ) : ℝ)) := by
    exact_mod_cast hlen
  have hbranch := branch_exponent_le (n := n) hDbranch
  have heqn : δ * ((n : ℝ) * D + 4) = ε / 3 * n + 4 * δ := by
    calc
      δ * ((n : ℝ) * D + 4) = (δ * D) * n + 4 * δ := by ring
      _ = ε / 3 * n + 4 * δ := by rw [hδD]
  have hsmall : ε / 3 * (n : ℝ) + ε / 3 * n ≤ ε * n := by
    have hrat : ε / 3 + ε / 3 ≤ ε := by linarith
    calc
      ε / 3 * (n : ℝ) + ε / 3 * n = (ε / 3 + ε / 3) * n := by ring
      _ ≤ ε * n := mul_le_mul_of_nonneg_right hrat (Nat.cast_nonneg n)
  have hExp : (((2 + 8 * n / D : ℕ) : ℝ)) +
      δ * ((n : ℝ) * D + 4) ≤ 2 + 4 * δ + ε * n := by
    rw [heqn]
    linarith
  have hsum :
      (formulas.map (fun φ =>
        (MainResults.timeMin C 2 φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
        (formulas.length : ℝ) *
          ((c : ℝ) * (2 : ℝ) ^ (δ * ((n : ℝ) * D + 4))) := by
    apply sum_le_length_mul
    intro φ hφ
    exact hc n φ (hvars φ hφ)
  calc
    (formulas.map (fun φ =>
        (MainResults.timeMin C 2 φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
        (formulas.length : ℝ) *
          ((c : ℝ) * (2 : ℝ) ^ (δ * ((n : ℝ) * D + 4))) := hsum
    _ ≤ (2 : ℝ) ^ (((2 + 8 * n / D : ℕ) : ℝ)) *
        ((c : ℝ) * (2 : ℝ) ^ (δ * ((n : ℝ) * D + 4))) :=
      mul_le_mul_of_nonneg_right hlenR (by positivity)
    _ = (c : ℝ) * (2 : ℝ) ^
        ((((2 + 8 * n / D : ℕ) : ℝ)) + δ * ((n : ℝ) * D + 4)) := by
      rw [Real.rpow_add (by norm_num)]
      ring
    _ ≤ (c : ℝ) * (2 : ℝ) ^ (2 + 4 * δ + ε * n) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg c)
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
    _ = ((c : ℝ) * (2 : ℝ) ^ (2 + 4 * δ)) *
        (2 : ℝ) ^ (ε * n) := by
      rw [Real.rpow_add (by norm_num)]
      ring
    _ ≤ (a : ℝ) * (2 : ℝ) ^ (ε * n) :=
      mul_le_mul_of_nonneg_right ha (by positivity)

/-- Any fixed polynomial overhead per query, plus one fixed polynomial term,
fits under the same exponential rate whenever the branch exponent is small. -/
theorem polynomial_overhead_budget (p D : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hD : 8 / (D : ℝ) ≤ ε / 3) :
    ∃ a : ℕ, ∀ (n : ℕ) (formulas : List StableMatching.CNF),
      formulas.length ≤ 2 ^ (2 + 8 * n / D) →
      ((n : ℝ) + 2) ^ p * ((formulas.length : ℝ) + 1) ≤
        (a : ℝ) * (2 : ℝ) ^ (ε * n) := by
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨c, hc⟩ := Wrap.Arith.poly_below p hthird
  refine ⟨8 * c, ?_⟩
  intro n formulas hlen
  let branch : ℝ := ((2 + 8 * n / D : ℕ) : ℝ)
  have hlenR : (formulas.length : ℝ) ≤ (2 : ℝ) ^ branch := by
    dsimp [branch]
    exact_mod_cast hlen
  have hbranch : branch ≤ 2 + ε / 3 * n := branch_exponent_le hD
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ branch := by
    apply Real.one_le_rpow (by norm_num)
    exact Nat.cast_nonneg _
  have hlenPlus : (formulas.length : ℝ) + 1 ≤ 2 * (2 : ℝ) ^ branch := by
    linarith
  have hsmall : ε / 3 * (n : ℝ) + ε / 3 * n ≤ ε * n := by
    have hrat : ε / 3 + ε / 3 ≤ ε := by linarith
    calc
      ε / 3 * (n : ℝ) + ε / 3 * n = (ε / 3 + ε / 3) * n := by ring
      _ ≤ ε * n := mul_le_mul_of_nonneg_right hrat (Nat.cast_nonneg n)
  have hExp : ε / 3 * (n : ℝ) + branch ≤ 2 + ε * n := by
    linarith
  calc
    ((n : ℝ) + 2) ^ p * ((formulas.length : ℝ) + 1) ≤
        ((c : ℝ) * (2 : ℝ) ^ (ε / 3 * n)) *
          (2 * (2 : ℝ) ^ branch) :=
      mul_le_mul (hc n) hlenPlus (by positivity) (by positivity)
    _ = (2 * (c : ℝ)) * (2 : ℝ) ^ (ε / 3 * n + branch) := by
      rw [Real.rpow_add (by norm_num)]
      ring
    _ ≤ (2 * (c : ℝ)) * (2 : ℝ) ^ (2 + ε * n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
    _ = ((8 * c : ℕ) : ℝ) * (2 : ℝ) ^ (ε * n) := by
      rw [Real.rpow_add (by norm_num)]
      norm_num
      ring

end StableMatching.CountingRates
