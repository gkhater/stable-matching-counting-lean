import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact finite-state identities used in the C25a signed reduction. -/

namespace StableMatching.Gadgets

/-- Compatibility of two independent-set bits. -/
def independentEdge (a b : Bool) : ℤ := if a && b then 0 else 1

def negativeWeight (a : Bool) : ℤ := if a then -1 else 1

/-- Sum over the three negative-weight internal vertices of a four-edge path. -/
def fourPath (u v : Bool) : ℤ :=
  ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
    independentEdge u a * independentEdge a b * independentEdge b c *
      independentEdge c v * negativeWeight a * negativeWeight b * negativeWeight c

/-- C25a (12): the path realizes the negative of one ordinary edge. -/
theorem fourPath_eq_neg_edge (u v : Bool) :
    fourPath u v = -independentEdge u v := by
  cases u <;> cases v <;> decide

abbrev PairState := Bool × Bool

/-- A cover vertex has two extensions when all three neighbors are covered. -/
def coverExtension (a b c : Bool) : ℤ := if a && b && c then 2 else 1

/-- The seven-vertex sign-removal cell, summed over its vertex `q`. -/
def cell (z : Bool) (i o : PairState) : ℤ :=
  ∑ q : Bool,
    coverExtension i.1 q o.2 * coverExtension i.2 z o.2 *
      coverExtension i.2 q o.1 * coverExtension i.1 z o.1

/-- Difference of the two terminal cover states, in the order 00, 01, 10, 11. -/
def signal (s : PairState) : ℤ :=
  if s = (false, true) then -1 else if s = (true, false) then 1 else 0

/-- C25a (17): each marked host vertex contributes its sign. -/
theorem cell_signal (z : Bool) (i : PairState) :
    (∑ o : PairState, cell z i o * signal o) =
      (if z then 1 else -1 : ℤ) * signal i := by
  cases z
  rcases i with ⟨a, b⟩
  cases a <;> cases b <;> decide
  rcases i with ⟨a, b⟩
  cases a <;> cases b <;> decide

def coverEdge (a b : Bool) : ℤ := if a || b then 1 else 0

/-- The side-change bridge consists of the two edges EE' and OO'. -/
def bridge (i o : PairState) : ℤ :=
  coverEdge i.1 o.1 * coverEdge i.2 o.2

/-- C25a (18): a side change negates the signal. -/
theorem bridge_signal (i : PairState) :
    (∑ o : PairState, bridge i o * signal o) = -signal i := by
  rcases i with ⟨a, b⟩
  cases a <;> cases b <;> decide

/-- With the selector uncovered, the input vector is (0,0,1,1). -/
def selectorInput (i : PairState) : ℤ := if i.1 then 1 else 0

/-- The final selector contraction has unit amplitude. -/
theorem selector_signal :
    (∑ i : PairState, selectorInput i * signal i) = 1 := by
  decide

/-- Any interface step that carries the difference signal by one scalar. -/
structure SignalStep where
  matrix : PairState → PairState → ℤ
  factor : ℤ
  carries : ∀ i, (∑ o : PairState, matrix i o * signal o) = factor * signal i

def signCell (z : Bool) : SignalStep where
  matrix := cell z
  factor := if z then 1 else -1
  carries := cell_signal z

def sideBridge : SignalStep where
  matrix := bridge
  factor := -1
  carries := by
    intro i
    simpa using bridge_signal i

/-- Contract a finite sequence from right to left against the terminal signal. -/
def chainAction : List SignalStep → PairState → ℤ
  | [], i => signal i
  | step :: rest, i => ∑ o : PairState, step.matrix i o * chainAction rest o

/-- C25a (17)–(18) compose without any assumption on the order of cells and bridges. -/
theorem chainAction_signal (steps : List SignalStep) (i : PairState) :
    chainAction steps i = (steps.map SignalStep.factor).prod * signal i := by
  induction steps generalizing i with
  | nil => simp [chainAction]
  | cons step rest ih =>
    simp only [chainAction, List.map_cons, List.prod_cons]
    simp_rw [ih]
    calc
      (∑ o : PairState,
          step.matrix i o * ((rest.map SignalStep.factor).prod * signal o)) =
          (rest.map SignalStep.factor).prod *
            (∑ o : PairState, step.matrix i o * signal o) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro o _
        ac_rfl
      _ = step.factor * (rest.map SignalStep.factor).prod * signal i := by
        rw [step.carries]
        ac_rfl

/-- Closing the selector extracts precisely the product of the step factors. -/
theorem selector_chain (steps : List SignalStep) :
    (∑ i : PairState, selectorInput i * chainAction steps i) =
      (steps.map SignalStep.factor).prod := by
  simp_rw [chainAction_signal]
  calc
    (∑ i : PairState,
        selectorInput i * ((steps.map SignalStep.factor).prod * signal i)) =
        (steps.map SignalStep.factor).prod *
          (∑ i : PairState, selectorInput i * signal i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ac_rfl
    _ = (steps.map SignalStep.factor).prod := by simp [selector_signal]

end StableMatching.Gadgets

#print axioms StableMatching.Gadgets.fourPath_eq_neg_edge
#print axioms StableMatching.Gadgets.cell_signal
#print axioms StableMatching.Gadgets.bridge_signal
#print axioms StableMatching.Gadgets.selector_signal
#print axioms StableMatching.Gadgets.chainAction_signal
#print axioms StableMatching.Gadgets.selector_chain
