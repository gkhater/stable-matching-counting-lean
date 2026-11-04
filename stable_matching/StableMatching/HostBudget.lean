import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import ToTuring.Bound

/-! Polynomial Turing simulation overhead preserves the uniform exponent. -/

namespace StableMatching.HostBudget

open Groundwork

theorem polynomial_exponential_budget {f : Nat → Nat} (hf : PB f) :
    ∃ a : Nat, ∀ (L B : Nat) (E : ℝ), 0 ≤ E →
      (B : ℝ) ≤ ((L : ℝ) + 3) * (2 : ℝ) ^ E →
      (f B : ℝ) ≤ (a : ℝ) * ((L : ℝ) + 4) ^ a * (2 : ℝ) ^ ((a : ℝ) * E) := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨a, ?_⟩
  intro L B E hE hB
  have hone : 1 ≤ (2 : ℝ) ^ E := Real.one_le_rpow (by norm_num) hE
  have hplus : (B : ℝ) + 1 ≤ ((L : ℝ) + 4) * (2 : ℝ) ^ E := by nlinarith
  have hp : (f B : ℝ) ≤ (a : ℝ) * ((B : ℝ) + 1) ^ a := by exact_mod_cast ha B
  have hpow : ((2 : ℝ) ^ E) ^ a = (2 : ℝ) ^ ((a : ℝ) * E) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  calc
    (f B : ℝ) ≤ (a : ℝ) * ((B : ℝ) + 1) ^ a := hp
    _ ≤ (a : ℝ) * (((L : ℝ) + 4) * (2 : ℝ) ^ E) ^ a := by gcongr
    _ = _ := by rw [mul_pow, hpow]; ring

theorem simulation_bound (q p L T S : Nat) (a b E : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hT : (T : ℝ) + 1 ≤ a * (2 : ℝ) ^ E)
    (hS : (L : ℝ) + S + 1 ≤ b * ((L : ℝ) + 1) ^ p * (2 : ℝ) ^ E) :
    ((q * (T + 1) * (L + S + 1) ^ q : Nat) : ℝ) ≤
      (q : ℝ) * a * b ^ q * ((L : ℝ) + 1) ^ (p * q) *
        (2 : ℝ) ^ (((q : ℝ) + 1) * E) := by
  have hexp : 0 < (2 : ℝ) ^ E := Real.rpow_pos_of_pos (by norm_num) _
  have hpow : ((2 : ℝ) ^ E) ^ q = (2 : ℝ) ^ (E * (q : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hcombine : (2 : ℝ) ^ E * ((2 : ℝ) ^ E) ^ q =
      (2 : ℝ) ^ (((q : ℝ) + 1) * E) := by
    rw [hpow, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  calc
    ((q * (T + 1) * (L + S + 1) ^ q : Nat) : ℝ) =
        (q : ℝ) * ((T : ℝ) + 1) * ((L : ℝ) + S + 1) ^ q := by push_cast; rfl
    _ ≤ (q : ℝ) * (a * (2 : ℝ) ^ E) *
        (b * ((L : ℝ) + 1) ^ p * (2 : ℝ) ^ E) ^ q := by
      gcongr
    _ = (q : ℝ) * a * b ^ q * ((L : ℝ) + 1) ^ (p * q) *
        ((2 : ℝ) ^ E * ((2 : ℝ) ^ E) ^ q) := by
      simp only [mul_pow, pow_mul]
      ring
    _ = _ := by rw [hcombine]

end StableMatching.HostBudget
