import StableMatching.Transfer
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A conditional exact counting algorithm interface. No algorithmic premise is hidden as an axiom. -/

namespace StableMatching

open MathEconLib.Matching

/-- An exact #SAT counter with a step bound indexed by its number of variables.
This is abstract; no result from Anthropic's Lean 4.33.1 development is imported. -/
structure SATCounter where
  run : CNF → ℕ
  steps : CNF → ℕ
  timeBound : ℕ → ℕ
  correct : ∀ φ, run φ = φ.satCount
  bound_mono : Monotone timeBound
  stepBound : ∀ φ, steps φ ≤ timeBound φ.numVars

/-- Assumed KOW branching and parsimonious chain-cut/radix encoding of every
residual leaf. Each leaf has a unique extension, expressed by `countPreserving`. -/
structure KOWEncoding {M W : Type*} [Fintype M] [Fintype W]
    (mkt : MarriageMarket M W) (Leaf : Type*) [Fintype Leaf] where
  leaves : Finset Leaf
  encode : Leaf → CNF
  countPreserving : Fintype.card mkt.StableMatching =
    ∑ leaf ∈ leaves, (encode leaf).satCount
  branchSteps : ℕ
  encodingSteps : Leaf → ℕ
  branchBudget : ℕ
  leafLimit : ℕ
  variableLimit : ℕ
  encodingBudget : ℕ
  branchBound : branchSteps ≤ branchBudget
  leafBound : leaves.card ≤ leafLimit
  variableBound : ∀ leaf ∈ leaves, (encode leaf).numVars ≤ variableLimit
  encodingBound : ∀ leaf ∈ leaves, encodingSteps leaf ≤ encodingBudget

namespace KOWEncoding

variable {M W Leaf : Type*} [Fintype M] [Fintype W] [Fintype Leaf]
variable {mkt : MarriageMarket M W}

def count (e : KOWEncoding mkt Leaf) (counter : SATCounter) : ℕ :=
  ∑ leaf ∈ e.leaves, counter.run (e.encode leaf)

def steps (e : KOWEncoding mkt Leaf) (counter : SATCounter) : ℕ :=
  e.branchSteps +
    ∑ leaf ∈ e.leaves, (e.encodingSteps leaf + counter.steps (e.encode leaf))

theorem count_correct (e : KOWEncoding mkt Leaf) (counter : SATCounter) :
    e.count counter = Fintype.card mkt.StableMatching := by
  simp only [count, counter.correct]
  exact e.countPreserving.symm

theorem steps_bound (e : KOWEncoding mkt Leaf) (counter : SATCounter) :
    e.steps counter ≤ e.branchBudget +
      e.leafLimit * (e.encodingBudget + counter.timeBound e.variableLimit) := by
  have hleaf : ∀ leaf ∈ e.leaves,
      e.encodingSteps leaf + counter.steps (e.encode leaf) ≤
        e.encodingBudget + counter.timeBound e.variableLimit := by
    intro leaf hmem
    exact Nat.add_le_add (e.encodingBound leaf hmem)
      ((counter.stepBound (e.encode leaf)).trans
        (counter.bound_mono (e.variableBound leaf hmem)))
  calc
    e.steps counter ≤ e.branchBudget +
        ∑ leaf ∈ e.leaves,
          (e.encodingBudget + counter.timeBound e.variableLimit) := by
      exact Nat.add_le_add e.branchBound (Finset.sum_le_sum hleaf)
    _ = e.branchBudget + e.leaves.card *
          (e.encodingBudget + counter.timeBound e.variableLimit) := by simp
    _ ≤ e.branchBudget + e.leafLimit *
          (e.encodingBudget + counter.timeBound e.variableLimit) := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right _ e.leafBound) _

end KOWEncoding
end StableMatching

#print axioms StableMatching.KOWEncoding.count_correct
#print axioms StableMatching.KOWEncoding.steps_bound
