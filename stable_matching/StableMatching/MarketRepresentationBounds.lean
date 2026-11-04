import StableMatching.RankInputCode
import MathEconLib.Matching.Classical.Marriage.RankRepresentation
import MathEconLib.Matching.Classical.Marriage.StableOrder

/-! Input and count bounds for the universal balanced-market rank witness. -/

namespace StableMatching.MarketRuntime

open Groundwork Turing MathEconLib.Matching MathEconLib.Matching.MarriageMarket

theorem representation_width {n : Nat}
    (mkt : MarriageMarket (Fin n) (Fin n)) :
    ∀ row ∈ (rankRepresentation mkt).men ++ (rankRepresentation mkt).women,
      ∀ v ∈ row, v < 2 ^ (n + 1) := by
  intro row hrow v hv
  have hbound := rankRepresentation_bound mkt
  have hvn : v ≤ n := by
    rcases List.mem_append.mp hrow with hm | hw
    · exact hbound.1 row hm v hv
    · exact hbound.2 row hw v hv
  exact (Nat.lt_succ_of_le hvn).trans
    (show n + 1 < 2 ^ (n + 1) from Nat.lt_two_pow_self)

private theorem card_castFin {a b : Nat} (h : a = b)
    (mkt : MarriageMarket (Fin a) (Fin a)) :
    Nat.card mkt.StableMatching = Nat.card (castFin h mkt).StableMatching := by
  cases h
  rfl

theorem representation_card {n : Nat}
    (mkt : MarriageMarket (Fin n) (Fin n)) :
    Nat.card (rankRepresentation mkt).market.StableMatching =
      Nat.card mkt.StableMatching := by
  calc
    Nat.card (rankRepresentation mkt).market.StableMatching =
        Nat.card (castFin (rankRepresentation_length mkt)
          (rankRepresentation mkt).market).StableMatching :=
      card_castFin (rankRepresentation_length mkt) _
    _ = Nat.card mkt.StableMatching := by rw [rankRepresentation_market]

theorem representation_input_length {n : Nat}
    (mkt : MarriageMarket (Fin n) (Fin n)) :
    (RankInputCode.encode (rankRepresentation mkt) (n + 1)).length + 4 ≤
      2 * (n + 4) ^ 3 := by
  rw [RankInputCode.encode_length, rankRepresentation_length]
  nlinarith [sq_nonneg (n : ℝ)]

theorem representation_input_length_real {n : Nat}
    (mkt : MarriageMarket (Fin n) (Fin n)) :
    ((RankInputCode.encode (rankRepresentation mkt) (n + 1)).length : ℝ) + 4 ≤
      2 * ((n : ℝ) + 4) ^ 3 := by
  exact_mod_cast representation_input_length mkt

end StableMatching.MarketRuntime
