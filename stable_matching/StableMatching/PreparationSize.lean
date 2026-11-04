import StableMatching.CNFNormalization
import StableMatching.CompactSize

/-! Explicit size bounds survive the exact-count-preserving SAT preparation. -/

namespace StableMatching

theorem CNF.prepare_clause_count (φ : CNF) :
    φ.prepare.clauses.length ≤ φ.clauses.length + φ.numVars + 8 := by
  calc
    φ.prepare.clauses.length ≤ φ.padFour.withOccurrenceTautologies.clauses.length :=
      φ.padFour.withOccurrenceTautologies.clauses.dedup_sublist.length_le
    _ = φ.clauses.length + φ.numVars + 8 := by
      simp [CNF.withOccurrenceTautologies, CNF.padFour]
      omega

def CNF.literalCount (φ : CNF) : Nat := (φ.clauses.map List.length).sum

theorem CNF.literalCount_le (φ : CNF) (k : Nat)
    (hwidth : ∀ clause ∈ φ.clauses, clause.length ≤ k) :
    φ.literalCount ≤ φ.clauses.length * k := by
  rcases φ with ⟨n, clauses⟩
  change (clauses.map List.length).sum ≤ clauses.length * k
  induction clauses with
  | nil => simp
  | cons clause clauses ih =>
    have hc := hwidth clause (by simp)
    have ht := ih (fun c hc => hwidth c (by simp [hc]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

namespace CompactSize

open MathEconLib.Matching

theorem prepared_clause_count {m n : Nat} (mkt : MarriageMarket (Fin m) (Fin n))
    (D : Nat) (hD : 0 < D) (ℓ : Nat) :
    ∀ φ ∈ CompactReduction.reduce mkt D hD ℓ,
      φ.prepare.clauses.length ≤
        (m * D) * 2 ^ ℓ + ((m * D) * 2 ^ ℓ) * ((m * D) * 2 ^ ℓ) +
          2 * m * ℓ + 8 := by
  intro φ hφ
  have hc := reduce_clause_count mkt D hD ℓ φ hφ
  have hv := CompactReduction.reduce_variable_bound mkt D hD ℓ φ hφ
  exact φ.prepare_clause_count.trans (by omega)

theorem prepared_literal_count {m n : Nat} (mkt : MarriageMarket (Fin m) (Fin n))
    (D : Nat) (hD : 0 < D) (ℓ : Nat) :
    ∀ φ ∈ CompactReduction.reduce mkt D hD ℓ,
      φ.prepare.literalCount ≤
        ((m * D) * 2 ^ ℓ + ((m * D) * 2 ^ ℓ) * ((m * D) * 2 ^ ℓ) +
          2 * m * ℓ + 8) * max (2 * ℓ) 2 := by
  intro φ hφ
  exact (φ.prepare.literalCount_le _
    (φ.prepare_width _ (CompactReduction.reduce_width mkt D hD ℓ φ hφ))).trans
      (Nat.mul_le_mul_right _ (prepared_clause_count mkt D hD ℓ φ hφ))

end CompactSize
end StableMatching
