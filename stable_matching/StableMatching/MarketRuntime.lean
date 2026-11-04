import StableMatching.UniformRuntime
import StableMatching.MarketRepresentationBounds

/-! The fixed rank-input counter covers every existing balanced marriage market. -/

namespace StableMatching.MarketRuntime

open Groundwork Turing MathEconLib.Matching MathEconLib.Matching.MarriageMarket

/-- One finite-alphabet machine counts stable matchings for every existing
balanced market. Its input is the rank representation supplied above. -/
theorem exists_market_counter :
    ∃ (N : TM2ComputableAux Bool Bool) (a : Nat),
      (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ c : Nat, ∀ {n : Nat}
        (mkt : MarriageMarket (Fin n) (Fin n)), 1 ≤ n →
        ∃ T : Nat,
          Wrap.Outputs N
            (RankInputCode.encode (rankRepresentation mkt) (n + 1))
            (Nat.bits (Nat.card mkt.StableMatching)) T ∧
          (T : ℝ) ≤ (c : ℝ) * ((n : ℝ) + 4) ^ (3 * a) *
            (2 : ℝ) ^ (ε * n) := by
  obtain ⟨N, a, hfinite, hrun⟩ := UniformRuntime.exists_subexponential_counter
  refine ⟨N, a, hfinite, ?_⟩
  intro ε hε
  obtain ⟨c, hc⟩ := hrun ε hε
  refine ⟨c * 2 ^ a, ?_⟩
  intro n mkt hn
  let p := rankRepresentation mkt
  have hb : ∀ row ∈ p.men ++ p.women, ∀ v ∈ row,
      v < 2 ^ (n + 1) := representation_width mkt
  have hp : 1 ≤ p.men.length := by
    rw [show p.men.length = n from rankRepresentation_length mkt]
    exact hn
  obtain ⟨T, hT, htime⟩ := hc p (n + 1) hb hp
  have hcount := representation_card mkt
  refine ⟨T, ?_, ?_⟩
  · simpa only [p, hcount] using hT
  · have hlen := representation_input_length_real mkt
    have hpow :
        (((RankInputCode.encode p (n + 1)).length : ℝ) + 4) ^ a ≤
          (2 * ((n : ℝ) + 4) ^ 3) ^ a := by
      gcongr
    have hrew : (2 * ((n : ℝ) + 4) ^ 3) ^ a =
        (2 : ℝ) ^ a * ((n : ℝ) + 4) ^ (3 * a) := by
      rw [mul_pow, ← pow_mul]
    have htime' : (T : ℝ) ≤ (c : ℝ) *
        (2 * ((n : ℝ) + 4) ^ 3) ^ a * (2 : ℝ) ^ (ε * n) := by
      calc
        (T : ℝ) ≤ (c : ℝ) *
            (((RankInputCode.encode p (n + 1)).length : ℝ) + 4) ^ a *
              (2 : ℝ) ^ (ε * n) := by
              simpa only [p, rankRepresentation_length] using htime
        _ ≤ _ := by gcongr
    rw [hrew] at htime'
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using htime'

/-- The participant polynomial is absorbed into an arbitrarily small extra
exponent. The finite-alphabet machine is chosen before the requested rate. -/
theorem exists_market_subexponential_counter :
    ∃ (N : TM2ComputableAux Bool Bool),
      (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ c : Nat, ∀ {n : Nat}
        (mkt : MarriageMarket (Fin n) (Fin n)), 1 ≤ n →
        ∃ T : Nat,
          Wrap.Outputs N
            (RankInputCode.encode (rankRepresentation mkt) (n + 1))
            (Nat.bits (Nat.card mkt.StableMatching)) T ∧
          (T : ℝ) ≤ (c : ℝ) * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨N, a, hfinite, hrun⟩ := exists_market_counter
  refine ⟨N, hfinite, ?_⟩
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨c₀, hc₀⟩ := hrun (ε / 2) hhalf
  obtain ⟨c₁, hc₁⟩ := Wrap.Arith.poly_below (3 * a) hhalf
  refine ⟨c₀ * 2 ^ (3 * a) * c₁, ?_⟩
  intro n mkt hn
  obtain ⟨T, hT, ht⟩ := hc₀ mkt hn
  refine ⟨T, hT, ?_⟩
  have hbase : (n : ℝ) + 4 ≤ 2 * ((n : ℝ) + 2) := by
    have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hpoly : ((n : ℝ) + 4) ^ (3 * a) ≤
      ((2 : ℝ) ^ (3 * a) * (c₁ : ℝ)) *
        (2 : ℝ) ^ ((ε / 2) * n) := by
    calc
      ((n : ℝ) + 4) ^ (3 * a) ≤
          (2 * ((n : ℝ) + 2)) ^ (3 * a) :=
        pow_le_pow_left₀ (by positivity) hbase _
      _ = (2 : ℝ) ^ (3 * a) * ((n : ℝ) + 2) ^ (3 * a) := by
        rw [mul_pow]
      _ ≤ (2 : ℝ) ^ (3 * a) *
          ((c₁ : ℝ) * (2 : ℝ) ^ ((ε / 2) * n)) :=
        mul_le_mul_of_nonneg_left (hc₁ n) (by positivity)
      _ = _ := by ring
  calc
    (T : ℝ) ≤ (c₀ : ℝ) * ((n : ℝ) + 4) ^ (3 * a) *
        (2 : ℝ) ^ ((ε / 2) * n) := ht
    _ ≤ (c₀ : ℝ) * (((2 : ℝ) ^ (3 * a) * (c₁ : ℝ)) *
        (2 : ℝ) ^ ((ε / 2) * n)) *
        (2 : ℝ) ^ ((ε / 2) * n) := by
      gcongr
    _ = ((c₀ * 2 ^ (3 * a) * c₁ : Nat) : ℝ) *
        (2 : ℝ) ^ (ε * n) := by
      have hexp : (2 : ℝ) ^ ((ε / 2) * n) *
          (2 : ℝ) ^ ((ε / 2) * n) = (2 : ℝ) ^ (ε * n) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      have hcast : ((c₀ * 2 ^ (3 * a) * c₁ : Nat) : ℝ) =
          (c₀ : ℝ) * (2 : ℝ) ^ (3 * a) * (c₁ : ℝ) := by
        push_cast
        ring
      rw [hcast, ← hexp]
      ring

end StableMatching.MarketRuntime

#print axioms StableMatching.MarketRuntime.exists_market_counter
#print axioms StableMatching.MarketRuntime.exists_market_subexponential_counter
