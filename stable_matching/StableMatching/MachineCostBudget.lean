import ToTuring.Bound

/-! The concrete host overhead is polynomial in the combined matching budget. -/

namespace StableMatching.MachineCostBudget

open Groundwork

theorem host_cost_polynomial (q a : Nat) (space words : Nat → Nat)
    (hspace : PB space) (hwords : PB words) :
    ∃ r : Nat → Nat, PB r ∧ ∀ (B L N V n Q W S : Nat),
      L ≤ B → N ≤ B → V ≤ B → n ≤ B → Q ≤ W → W ≤ words B → S ≤ space B →
      q * (N + 1 + (V + Q) + 1) *
        (L + (max (2 * L + 1 + S)
          (W + (n * n + 2) + (a * (W + 1) + a * V) + 1) + 1) + 1) ^ q ≤ r B := by
  let u : Nat → Nat := fun B => words B + (B ^ 2 + 2) +
    (a * (words B + 1) + a * B) + 1
  have hu : PB u :=
    ((hwords.add ((PB.id'.pow 2).add (PB.const 2))).add
      (((PB.const a).mul (hwords.add (PB.const 1))).add ((PB.const a).mul PB.id'))).add (PB.const 1)
  let first : Nat → Nat := fun B => 2 * B + words B + 3
  let second : Nat → Nat := fun B => 4 * B + space B + u B + 4
  have hfirst : PB first := (((PB.const 2).mul PB.id').add hwords).add (PB.const 3)
  have hsecond : PB second := ((((PB.const 4).mul PB.id').add hspace).add hu).add (PB.const 4)
  refine ⟨fun B => q * first B * second B ^ q, ((PB.const q).mul hfirst).mul (hsecond.pow q), ?_⟩
  intro B L N V n Q W S hL hN hV hn hQ hW hS
  have htime : N + 1 + (V + Q) + 1 ≤ first B := by dsimp [first]; omega
  have huBound : W + (n * n + 2) + (a * (W + 1) + a * V) + 1 ≤ u B := by
    dsimp [u]
    rw [pow_two]
    gcongr
  have hm : max (2 * L + 1 + S)
      (W + (n * n + 2) + (a * (W + 1) + a * V) + 1) ≤
        (2 * B + 1 + space B) + u B := by
    apply max_le <;> omega
  have hstate : L + (max (2 * L + 1 + S)
      (W + (n * n + 2) + (a * (W + 1) + a * V) + 1) + 1) + 1 ≤ second B := by
    dsimp [second]
    omega
  exact Nat.mul_le_mul (Nat.mul_le_mul_left q htime) (Nat.pow_le_pow_left hstate q)

end StableMatching.MachineCostBudget
