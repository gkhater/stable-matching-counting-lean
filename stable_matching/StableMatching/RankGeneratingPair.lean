import StableMatching.RankPosetMatrix
import MathEconLib.Matching.Classical.Marriage.ComputedChains

/-! Costed numeric witness pairs for the computed stable-matching irreducibles. -/

namespace StableMatching.RankDA

open Groundwork
open MathEconLib.Matching.MarriageMarket

def pairMatchesCode (input : Input) (code : List Nat) (pair : Nat × Nat) : Bool :=
  candidateCodes input pair.1 pair.2 == some code

def generatingPairCode (input : Input) (i : Nat) : Nat × Nat :=
  let code := (irreducibleCodes input).getD i []
  ((pairs input.1).find? (pairMatchesCode input code)).getD (0, 0)

@[fun_prop] theorem pairMatchesCode_polyT {α : Type} [Enc α]
    {input : α → Input} {code : α → List Nat} {pair : α → Nat × Nat}
    (hinput : PolyT input) (hcode : PolyT code) (hpair : PolyT pair) :
    PolyT (fun x => pairMatchesCode (input x) (code x) (pair x)) := by
  unfold pairMatchesCode
  fun_prop

theorem generatingPairCode_polyT :
    PolyT (fun p : Input × Nat => generatingPairCode p.1 p.2) := by
  have hc := irreducibleCodes_polyT
  unfold generatingPairCode
  fun_prop

theorem generatingPairCode_comp_polyT {α : Type} [Enc α]
    {input : α → Input} {i : α → Nat}
    (hinput : PolyT input) (hi : PolyT i) :
    PolyT (fun x => generatingPairCode (input x) (i x)) := by
  change PolyT ((fun p : Input × Nat => generatingPairCode p.1 p.2) ∘
    (fun x => (input x, i x)))
  exact Groundwork.PolyT.comp
    (f := fun p : Input × Nat => generatingPairCode p.1 p.2)
    (g := fun x : α => (input x, i x)) generatingPairCode_polyT
    (Groundwork.PolyT.prodMk hinput hi)

theorem irreducibleCode_getD (p : RankInput)
    (i : Fin (p.market.computedIrreducibles
      (List.finRange p.men.length) (List.finRange p.men.length)).length) :
    (irreducibleCodes (p.men, p.women)).getD i.val [] =
      matchingCodes ((p.market.computedIrreducibles
        (List.finRange p.men.length) (List.finRange p.men.length)).get i).matching := by
  rw [irreducibleCodes_correct]
  rw [List.getD_eq_getElem _ [] (by simp)]
  simp

theorem pairMatchesCode_correct (p : RankInput)
    (i : Fin (p.market.computedIrreducibles
      (List.finRange p.men.length) (List.finRange p.men.length)).length)
    (m w : Fin p.men.length) :
    pairMatchesCode (p.men, p.women)
      ((irreducibleCodes (p.men, p.women)).getD i.val []) (m.val, w.val) =
      p.market.pairMatches (List.finRange p.men.length)
        (List.finRange p.men.length) i (m, w) := by
  rw [irreducibleCode_getD]
  rw [pairMatchesCode, candidateCodes_correct]
  unfold MathEconLib.Matching.MarriageMarket.pairMatches
  let f := fun μ : p.market.StableMatching => matchingCodes μ.matching
  have hf : Function.Injective f := stableCodes_injective p.market
  cases hc : p.market.thresholdCandidate m w with
  | none => simp
  | some μ =>
    apply Bool.eq_iff_iff.mpr
    simp only [Option.map_some, beq_iff_eq, decide_eq_true_eq,
      Option.some.injEq]
    exact hf.eq_iff

private theorem find?_map {α β : Type*} (xs : List α) (f : α → β) (test : β → Bool) :
    (xs.map f).find? test = (xs.find? (fun a => test (f a))).map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, List.find?_cons]
    cases test (f a) <;> simp [ih]

theorem generatingPairCode_correct (p : RankInput)
    (i : Fin (p.market.computedIrreducibles
      (List.finRange p.men.length) (List.finRange p.men.length)).length) :
    generatingPairCode (p.men, p.women) i.val =
      let pair := p.market.generatingPair (List.finRange p.men.length)
        (List.finRange p.men.length) i
      (pair.1.val, pair.2.val) := by
  let pairVal : Fin p.men.length × Fin p.men.length → Nat × Nat :=
    fun pair => (pair.1.val, pair.2.val)
  have hfind :
      (pairs p.men).find? (pairMatchesCode (p.men, p.women)
        ((irreducibleCodes (p.men, p.women)).getD i.val [])) =
      (((List.finRange p.men.length).product (List.finRange p.men.length)).find?
        (p.market.pairMatches (List.finRange p.men.length)
          (List.finRange p.men.length) i)).map pairVal := by
    rw [pairs_finRange, find?_map]
    have hp : (fun q : Fin p.men.length × Fin p.men.length =>
        pairMatchesCode (p.men, p.women)
          ((irreducibleCodes (p.men, p.women)).getD i.val []) (q.1.val, q.2.val)) =
        p.market.pairMatches (List.finRange p.men.length)
          (List.finRange p.men.length) i := by
      funext q
      exact pairMatchesCode_correct p i q.1 q.2
    rw [hp]
    rfl
  change ((pairs p.men).find? (pairMatchesCode (p.men, p.women)
    ((irreducibleCodes (p.men, p.women)).getD i.val []))).getD (0, 0) = _
  rw [hfind]
  have hs := p.market.generatingPair_isSome
    (List.finRange p.men.length) (List.finRange p.men.length) i
  have heq :
      ((List.finRange p.men.length).product (List.finRange p.men.length)).find?
        (p.market.pairMatches (List.finRange p.men.length)
          (List.finRange p.men.length) i) =
      some (p.market.generatingPair (List.finRange p.men.length)
        (List.finRange p.men.length) i) :=
    (Option.coe_get hs).symm
  rw [heq]
  rfl

end StableMatching.RankDA
