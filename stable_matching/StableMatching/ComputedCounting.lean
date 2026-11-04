import StableMatching.Formula
import StableMatching.PosetEncoding
import MathEconLib.Matching.Classical.Marriage.ComputedPoset

/-!
# A computed parsimonious reduction from stable matchings to two-CNF

The variable set is the duplicate-free DA-generated irreducible list. All
formula construction is executable. Birkhoff's theorem and the computed-poset
correctness theorem prove count preservation; they are not algorithm inputs.
The variable bound is quadratic in participants. Subexponential counting still
requires the stopped-branching argument and its cost analysis.
-/

namespace StableMatching.ComputedCounting

open MathEconLib.Matching

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

def cnf (mkt : MarriageMarket M W) (men : List M) (women : List W) : CNF :=
  letI : LE (Fin (mkt.computedIrreducibles men women).length) :=
    (mkt.computedIrreducibleOrder men women).toLE
  letI : Preorder (Fin (mkt.computedIrreducibles men women).length) :=
    (mkt.computedIrreducibleOrder men women).toPreorder
  letI := mkt.computedIrreducibleDecidableLE men women
  PosetEncoding.cnf (Equiv.refl (Fin (mkt.computedIrreducibles men women).length))

theorem cnf_correct (mkt : MarriageMarket M W) (men : List M) (women : List W)
    (hmen : ∀ m : M, m ∈ men) (hwomen : ∀ w : W, w ∈ women) :
    (cnf mkt men women).satCount = Nat.card mkt.StableMatching := by
  let : LE (Fin (mkt.computedIrreducibles men women).length) :=
    (mkt.computedIrreducibleOrder men women).toLE
  let : Preorder (Fin (mkt.computedIrreducibles men women).length) :=
    (mkt.computedIrreducibleOrder men women).toPreorder
  let := mkt.computedIrreducibleDecidableLE men women
  let e := mkt.computedIrreducibleOrderIso men women hmen hwomen
  have hcard : Nat.card mkt.StableMatching =
      Nat.card (LowerSet (Fin (mkt.computedIrreducibles men women).length)) :=
    Nat.card_congr ((MarriageMarket.StableMatching.lowerSetSupIrred mkt).toEquiv.trans
      (LowerSet.map e.symm).toEquiv)
  exact (PosetEncoding.satCount_eq_card_lowerSet (Equiv.refl _)).trans hcard.symm

theorem cnf_width (mkt : MarriageMarket M W) (men : List M) (women : List W) :
    ∀ clause ∈ (cnf mkt men women).clauses, clause.length ≤ 2 := by
  let : LE (Fin (mkt.computedIrreducibles men women).length) :=
    (mkt.computedIrreducibleOrder men women).toLE
  let : Preorder (Fin (mkt.computedIrreducibles men women).length) :=
    (mkt.computedIrreducibleOrder men women).toPreorder
  let := mkt.computedIrreducibleDecidableLE men women
  exact PosetEncoding.clause_width (Equiv.refl (Fin (mkt.computedIrreducibles men women).length))

theorem cnf_numVars_le (mkt : MarriageMarket M W) (men : List M) (women : List W) :
    (cnf mkt men women).numVars ≤ men.length * women.length :=
  mkt.computedIrreducibles_length men women

theorem cnf_clause_count (mkt : MarriageMarket M W) (men : List M) (women : List W) :
    (cnf mkt men women).clauses.length ≤ (men.length * women.length) ^ 2 := by
  let : LE (Fin (mkt.computedIrreducibles men women).length) :=
    (mkt.computedIrreducibleOrder men women).toLE
  let : Preorder (Fin (mkt.computedIrreducibles men women).length) :=
    (mkt.computedIrreducibleOrder men women).toPreorder
  let := mkt.computedIrreducibleDecidableLE men women
  have h := PosetEncoding.clause_count
    (Equiv.refl (Fin (mkt.computedIrreducibles men women).length))
  simpa only [cnf, pow_two] using h.trans
    (Nat.mul_self_le_mul_self (mkt.computedIrreducibles_length men women))

/-- Numeric participant types supply explicit exhaustive lists. -/
def finiteCnf {m n : Nat} (mkt : MarriageMarket (Fin m) (Fin n)) : CNF :=
  cnf mkt (List.finRange m) (List.finRange n)

theorem finiteCnf_correct {m n : Nat} (mkt : MarriageMarket (Fin m) (Fin n)) :
    (finiteCnf mkt).satCount = Nat.card mkt.StableMatching :=
  cnf_correct mkt _ _ (fun _ => List.mem_finRange _) (fun _ => List.mem_finRange _)

theorem finiteCnf_numVars_le {m n : Nat} (mkt : MarriageMarket (Fin m) (Fin n)) :
    (finiteCnf mkt).numVars ≤ m * n := by
  simpa only [finiteCnf, List.length_finRange] using cnf_numVars_le mkt (List.finRange m) (List.finRange n)

end StableMatching.ComputedCounting
