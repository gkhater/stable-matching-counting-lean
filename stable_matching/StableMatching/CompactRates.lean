import StableMatching.CountingRates
import Mathlib.Data.Nat.Log

/-!
# Numerical budget for compact chain-cut counting queries

The compact encoding has a fixed width `max (2 * ℓ) 2` and at most
`2 * n * ℓ` variables. This module absorbs the width and the tree's
branch count into any positive exponential rate.
-/

namespace StableMatching.CompactRates

/-- The SAT time is bounded by its variable-side term at any fixed width. -/
theorem timeMin_le_rate (C k m N : ℕ) :
    (MainResults.timeMin C k m N : ℝ) ≤
      (2 : ℝ) ^ (((C : ℝ) * (k : ℝ) ^ 2) *
        ((N : ℝ) * MainTheoremForms.lg (MainTheoremForms.lg N) /
          Real.sqrt (MainTheoremForms.lg N))) := by
  unfold MainResults.timeMin
  calc
    (↑⌊(2 : ℝ) ^ ((C : ℝ) *
        min (MainResults.expM k m) (MainResults.expN k N))⌋₊ : ℝ) ≤
        (2 : ℝ) ^ ((C : ℝ) *
          min (MainResults.expM k m) (MainResults.expN k N)) :=
      Nat.floor_le (by positivity)
    _ ≤ (2 : ℝ) ^ ((C : ℝ) * MainResults.expN k N) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg C))
    _ = (2 : ℝ) ^ (((C : ℝ) * (k : ℝ) ^ 2) *
          ((N : ℝ) * MainTheoremForms.lg (MainTheoremForms.lg N) /
            Real.sqrt (MainTheoremForms.lg N))) := by
      congr 1
      unfold MainResults.expN MainResults.lg MainTheoremForms.lg
      ring

/-- A prepared query with at most `n*L` original variables fits any positive
rate at each fixed SAT width. -/
theorem prepared_query_le (C k L : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℕ, ∀ (n : ℕ) (φ : StableMatching.CNF),
      φ.numVars ≤ n * L →
      (MainResults.timeMin C k φ.prepare.clauses.length φ.prepare.numVars : ℝ) ≤
        (c : ℝ) * (2 : ℝ) ^ (δ * ((n : ℝ) * L + 4)) := by
  obtain ⟨c, hc⟩ := Wrap.Arith.rate_below
    (B := (C : ℝ) * (k : ℝ) ^ 2) (ε := δ) (by positivity) hδ
  refine ⟨c, ?_⟩
  intro n φ hvars
  have hN4 : 4 ≤ φ.prepare.numVars := by simp
  have hN : (φ.prepare.numVars : ℝ) ≤ (n : ℝ) * L + 4 := by
    have hnat : φ.prepare.numVars ≤ n * L + 4 := by
      simpa only [StableMatching.CNF.prepare_numVars] using
        Nat.add_le_add_right hvars 4
    exact_mod_cast hnat
  calc
    (MainResults.timeMin C k φ.prepare.clauses.length φ.prepare.numVars : ℝ) ≤
        (2 : ℝ) ^ (((C : ℝ) * (k : ℝ) ^ 2) *
          ((φ.prepare.numVars : ℝ) *
            MainTheoremForms.lg (MainTheoremForms.lg φ.prepare.numVars) /
              Real.sqrt (MainTheoremForms.lg φ.prepare.numVars))) :=
      timeMin_le_rate C _ _ _
    _ ≤ (c : ℝ) * (2 : ℝ) ^ (δ * φ.prepare.numVars) :=
      hc _ hN4
    _ ≤ (c : ℝ) * (2 : ℝ) ^ (δ * ((n : ℝ) * L + 4)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg c)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_left hN hδ.le

/-- The least binary width for a positive block length is the upper base-two
logarithm of the number of possible cut values. -/
theorem exists_bit_width (D : ℕ) (hD : 0 < D) :
    ∃ ℓ : ℕ, ℓ = Nat.clog 2 (D + 1) ∧ 0 < ℓ ∧ D + 1 ≤ 2 ^ ℓ := by
  refine ⟨Nat.clog 2 (D + 1), rfl, ?_, ?_⟩
  · exact Nat.clog_pos Nat.one_lt_two (by omega)
  · exact Nat.le_pow_clog Nat.one_lt_two (D + 1)

/-- List summation converts a common per-query time bound to a length factor. -/
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

/-- Fixed compact width and branch count fit under any positive exponential
rate. The width depends only on the requested rate. -/
theorem oracle_list_budget (C : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D ℓ : ℕ, 0 < D ∧ ℓ = Nat.clog 2 (D + 1) ∧ 0 < ℓ ∧ D + 1 ≤ 2 ^ ℓ ∧
      8 / (D : ℝ) ≤ ε / 3 ∧ ∃ a : ℕ,
      ∀ (n : ℕ), 1 ≤ n → ∀ (formulas : List StableMatching.CNF),
        formulas.length ≤ 2 ^ (2 + 8 * n / D) →
        (∀ φ ∈ formulas, φ.numVars ≤ 2 * n * ℓ) →
        (formulas.map (fun φ =>
          (MainResults.timeMin C (max (2 * ℓ) 2)
            φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
          (a : ℝ) * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨D, hDpos, hDbranch⟩ := CountingRates.exists_block_length hε
  obtain ⟨ℓ, hℓclog, hℓpos, hℓbits⟩ := exists_bit_width D hDpos
  let L : ℕ := 2 * ℓ
  let k : ℕ := max L 2
  let δ : ℝ := ε / (3 * (L : ℝ))
  have hLreal : (0 : ℝ) < L := by
    dsimp [L]
    exact_mod_cast Nat.mul_pos (by omega : 0 < 2) hℓpos
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδL : δ * (L : ℝ) = ε / 3 := by
    dsimp [δ]
    field_simp
  obtain ⟨c, hc⟩ := prepared_query_le C k L hδ
  obtain ⟨a, ha⟩ := exists_nat_ge
    ((c : ℝ) * (2 : ℝ) ^ (2 + 4 * δ))
  refine ⟨D, ℓ, hDpos, hℓclog, hℓpos, hℓbits, hDbranch, a, ?_⟩
  intro n _hn formulas hlen hvars
  have hlenR : (formulas.length : ℝ) ≤
      (2 : ℝ) ^ (((2 + 8 * n / D : ℕ) : ℝ)) := by
    exact_mod_cast hlen
  have hbranch := CountingRates.branch_exponent_le (n := n) hDbranch
  have heqn : δ * ((n : ℝ) * L + 4) = ε / 3 * n + 4 * δ := by
    calc
      δ * ((n : ℝ) * L + 4) = (δ * L) * n + 4 * δ := by ring
      _ = ε / 3 * n + 4 * δ := by rw [hδL]
  have hsmall : ε / 3 * (n : ℝ) + ε / 3 * n ≤ ε * n := by
    have hrat : ε / 3 + ε / 3 ≤ ε := by linarith
    calc
      ε / 3 * (n : ℝ) + ε / 3 * n = (ε / 3 + ε / 3) * n := by ring
      _ ≤ ε * n := mul_le_mul_of_nonneg_right hrat (Nat.cast_nonneg n)
  have hExp : (((2 + 8 * n / D : ℕ) : ℝ)) +
      δ * ((n : ℝ) * L + 4) ≤ 2 + 4 * δ + ε * n := by
    rw [heqn]
    linarith
  have hsum :
      (formulas.map (fun φ =>
        (MainResults.timeMin C (max (2 * ℓ) 2)
          φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
        (formulas.length : ℝ) *
          ((c : ℝ) * (2 : ℝ) ^ (δ * ((n : ℝ) * L + 4))) := by
    apply sum_le_length_mul
    intro φ hφ
    change (MainResults.timeMin C k
        φ.prepare.clauses.length φ.prepare.numVars : ℝ) ≤ _
    apply hc n φ
    simpa only [L, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hvars φ hφ
  calc
    (formulas.map (fun φ =>
        (MainResults.timeMin C (max (2 * ℓ) 2)
          φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
        (formulas.length : ℝ) *
          ((c : ℝ) * (2 : ℝ) ^ (δ * ((n : ℝ) * L + 4))) := hsum
    _ ≤ (2 : ℝ) ^ (((2 + 8 * n / D : ℕ) : ℝ)) *
        ((c : ℝ) * (2 : ℝ) ^ (δ * ((n : ℝ) * L + 4))) :=
      mul_le_mul_of_nonneg_right hlenR (by positivity)
    _ = (c : ℝ) * (2 : ℝ) ^
        ((((2 + 8 * n / D : ℕ) : ℝ)) + δ * ((n : ℝ) * L + 4)) := by
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

/-- The same block length also absorbs a fixed polynomial overhead for each
query and one final polynomial term. -/
theorem oracle_and_overhead_budget (C p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D ℓ : ℕ, 0 < D ∧ ℓ = Nat.clog 2 (D + 1) ∧ 0 < ℓ ∧ D + 1 ≤ 2 ^ ℓ ∧
      ∃ a b : ℕ, ∀ (n : ℕ), 1 ≤ n → ∀ (formulas : List StableMatching.CNF),
        formulas.length ≤ 2 ^ (2 + 8 * n / D) →
        (∀ φ ∈ formulas, φ.numVars ≤ 2 * n * ℓ) →
        (formulas.map (fun φ =>
          (MainResults.timeMin C (max (2 * ℓ) 2)
            φ.prepare.clauses.length φ.prepare.numVars : ℝ))).sum ≤
            (a : ℝ) * (2 : ℝ) ^ (ε * n) ∧
        ((n : ℝ) + 2) ^ p * ((formulas.length : ℝ) + 1) ≤
            (b : ℝ) * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨D, ℓ, hDpos, hℓclog, hℓpos, hℓbits, hDbranch, a, ha⟩ :=
    oracle_list_budget C hε
  obtain ⟨b, hb⟩ := CountingRates.polynomial_overhead_budget p D hε hDbranch
  refine ⟨D, ℓ, hDpos, hℓclog, hℓpos, hℓbits, a, b, ?_⟩
  intro n hn formulas hlen hvars
  exact ⟨ha n hn formulas hlen hvars, hb n formulas hlen⟩

end StableMatching.CompactRates
