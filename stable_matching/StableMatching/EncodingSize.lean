import StableMatching.PreparationSize
import StableMatching.AnthropicBridge

/-! Length of the actual Boolean input word used by the Anthropic machine. -/

namespace MainResults

theorem encClauses_length (k : Nat) {n : Nat} (φ : CNF n) :
    (encClauses k φ).length = n + 1 + φ.length * k * (Nat.log2 (2 * n) + 1) := by
  unfold encClauses
  simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_flatMap, List.length_map, List.length_range]
  simp
  ring

theorem encInput_length (k : Nat) {n : Nat} (φ : CNF n) :
    (encInput k φ).length = k + n + 2 + φ.length * k * (Nat.log2 (2 * n) + 1) := by
  simp only [encInput, List.length_append, List.length_replicate, List.length_cons,
    encClauses_length]
  omega

theorem encInput_length_le (k : Nat) {n : Nat} (φ : CNF n) :
    (encInput k φ).length ≤ k + n + 2 + φ.length * k * (2 * n + 1) := by
  rw [encInput_length]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log2_le_self (2 * n)) 1)) _

end MainResults

namespace StableMatching.CompactSize

open MathEconLib.Matching

theorem prepared_input_length {m n : Nat} (mkt : MarriageMarket (Fin m) (Fin n))
    (D : Nat) (hD : 0 < D) (ℓ : Nat) :
    ∀ φ ∈ CompactReduction.reduce mkt D hD ℓ,
      (MainResults.encInput (max (2 * ℓ) 2) φ.prepare.clauses).length ≤
        max (2 * ℓ) 2 + (2 * m * ℓ + 4) + 2 +
          ((m * D) * 2 ^ ℓ + ((m * D) * 2 ^ ℓ) * ((m * D) * 2 ^ ℓ) +
            2 * m * ℓ + 8) * max (2 * ℓ) 2 * (2 * (2 * m * ℓ + 4) + 1) := by
  intro φ hφ
  have hvars : φ.prepare.numVars ≤ 2 * m * ℓ + 4 := by
    simpa only [CNF.prepare_numVars] using
      Nat.add_le_add_right (CompactReduction.reduce_variable_bound mkt D hD ℓ φ hφ) 4
  have hclauses := prepared_clause_count mkt D hD ℓ φ hφ
  exact (MainResults.encInput_length_le (max (2 * ℓ) 2) φ.prepare.clauses).trans
    (Nat.add_le_add (by omega)
      (Nat.mul_le_mul (Nat.mul_le_mul_right _ hclauses) (by omega)))

end StableMatching.CompactSize
