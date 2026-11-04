import StableMatching.RankPartners
import MathEconLib.Matching.Classical.Marriage.IrreducibleComputation

/-! Costed canonical vectors for the actual threshold-generator routine. -/

namespace StableMatching.RankDA

open MathEconLib.Matching
open MathEconLib.Matching.MarriageMarket
open Groundwork
open RankInputComplexity

def thresholdCodes (input : Input) (m threshold : Nat) : List Nat :=
  partnerCodes input.1 (thresholdOutput input m threshold)

def bottomCodes (input : Input) : List Nat :=
  partnerCodes input.1 (womanOutput input)

def candidateCodes (input : Input) (m threshold : Nat) : Option (List Nat) :=
  if rankAt input.1 m input.1.length < rankAt input.1 m threshold then
    let codes := thresholdCodes input m threshold
    if codes.getD m input.1.length = input.1.length then none else some codes
  else none

@[fun_prop] theorem thresholdCodes_polyT {α : Type} [Enc α]
    {input : α → Input} {m t : α → Nat}
    (hinput : PolyT input) (hm : PolyT m) (ht : PolyT t) :
    PolyT (fun x => thresholdCodes (input x) (m x) (t x)) := by
  unfold thresholdCodes
  fun_prop

@[fun_prop] theorem bottomCodes_polyT {α : Type} [Enc α] {input : α → Input}
    (hinput : PolyT input) : PolyT (fun x => bottomCodes (input x)) := by
  have hw := womanOutput_polyT
  unfold bottomCodes
  fun_prop

@[fun_prop] theorem candidateCodes_polyT {α : Type} [Enc α]
    {input : α → Input} {m t : α → Nat}
    (hinput : PolyT input) (hm : PolyT m) (ht : PolyT t) :
    PolyT (fun x => candidateCodes (input x) (m x) (t x)) := by
  unfold candidateCodes
  fun_prop

theorem thresholdCodes_correct (p : RankInput) (m t : Fin p.men.length) :
    thresholdCodes (p.men, p.women) m.val t.val = matchingCodes (p.market.thresholdDA m t) :=
  partnerCodes_correct p.men rfl _ _ (threshold_output_bounded p m t)
    (threshold_output_matching p m t)

theorem bottomCodes_correct (p : RankInput) :
    bottomCodes (p.men, p.women) = matchingCodes p.market.womanGaleShapleyComputable :=
  partnerCodes_correct p.men rfl _ _ (woman_output_bounded p) (woman_output_matching p)

theorem candidateCodes_correct (p : RankInput) (m t : Fin p.men.length) :
    candidateCodes (p.men, p.women) m.val t.val =
      (p.market.thresholdCandidate m t).map (fun μ => matchingCodes μ.matching) := by
  have hacc : p.market.ltM m none (some t) =
      (rankAt p.men m.val p.men.length < rankAt p.men m.val t.val) :=
    propext (p.ltM_iff m none (some t))
  simp only [candidateCodes, thresholdCodes_correct, matchingCodes_getD, optionIndex_eq_n_iff]
  unfold MarriageMarket.thresholdCandidate
  split_ifs <;> simp_all
  · exact hacc
  · intro h
    exact (hacc h).elim

end StableMatching.RankDA
