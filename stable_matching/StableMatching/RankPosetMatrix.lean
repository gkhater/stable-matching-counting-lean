import StableMatching.RankPosetComputation
import MathEconLib.Matching.Classical.Marriage.ComputedPoset

/-! Polynomial-time construction of the computed irreducible comparison table. -/

namespace StableMatching.RankDA

open MathEconLib.Matching
open MathEconLib.Matching.MarriageMarket
open Groundwork
open RankInputComplexity

def codeLe (rows : Rows) (a b : List Nat) : Bool :=
  (participants rows).all (fun m => decide
    (rankAt rows m (a.getD m rows.length) ≤ rankAt rows m (b.getD m rows.length)))

def orderRows (input : Input) : List (List Bool) :=
  let codes := irreducibleCodes input
  codes.map (fun a => codes.map (fun b => codeLe input.1 a b))

@[fun_prop] theorem codeLe_polyT {α : Type} [Enc α]
    {rows : α → Rows} {a b : α → List Nat}
    (hrows : PolyT rows) (ha : PolyT a) (hb : PolyT b) :
    PolyT (fun x => codeLe (rows x) (a x) (b x)) := by
  unfold codeLe
  fun_prop

theorem orderRows_polyT : PolyT orderRows := by
  have hc := irreducibleCodes_polyT
  unfold orderRows
  fun_prop

theorem codeLe_matching_iff (p : RankInput)
    (μ ν : Fin p.men.length ≃. Fin p.men.length) :
    codeLe p.men (matchingCodes μ) (matchingCodes ν) = true ↔
      ∀ m, p.market.leM m (μ m) (ν m) := by
  unfold codeLe
  rw [List.all_eq_true]
  constructor
  · intro h m
    have hm := h m.val (by simp [participants])
    have hle := of_decide_eq_true hm
    rw [matchingCodes_getD μ m _, matchingCodes_getD ν m _] at hle
    exact (p.leM_iff m (μ m) (ν m)).mpr hle
  · intro h m hm
    have hlt : m < p.men.length := by simpa [participants] using hm
    let i : Fin p.men.length := ⟨m, hlt⟩
    have hle := (p.leM_iff i (μ i) (ν i)).mp (h i)
    apply decide_eq_true
    change rankAt p.men i.val ((matchingCodes μ).getD i.val p.men.length) ≤
      rankAt p.men i.val ((matchingCodes ν).getD i.val p.men.length)
    rw [matchingCodes_getD μ i _, matchingCodes_getD ν i _]
    exact hle

theorem irreducibleCodes_length_bound (p : RankInput) :
    (irreducibleCodes (p.men, p.women)).length ≤ p.men.length * p.men.length := by
  rw [irreducibleCodes_correct, List.length_map]
  simpa only [List.length_finRange] using p.market.computedIrreducibles_length
    (List.finRange p.men.length) (List.finRange p.men.length)

theorem orderRows_entry (p : RankInput)
    (i j : Fin (p.market.computedIrreducibles
      (List.finRange p.men.length) (List.finRange p.men.length)).length) :
    ((orderRows (p.men, p.women)).getD i.val []).getD j.val false = true ↔
      @LE.le _ (p.market.computedIrreducibleOrder
        (List.finRange p.men.length) (List.finRange p.men.length)).toLE i j := by
  unfold orderRows
  rw [irreducibleCodes_correct]
  rw [List.getD_eq_getElem _ [] (by simp)]
  simp only [List.getElem_map]
  rw [List.getD_eq_getElem _ false (by simp)]
  simp only [List.getElem_map]
  rw [codeLe_matching_iff]
  rfl

end StableMatching.RankDA

#print axioms StableMatching.RankDA.orderRows_polyT
#print axioms StableMatching.RankDA.orderRows_entry
