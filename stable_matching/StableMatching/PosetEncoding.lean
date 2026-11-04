import StableMatching.Formula
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.SetTheory.Cardinal.Finite

/-!
# A parsimonious Boolean encoding of finite lower sets

An explicit indexing equivalence supplies the variable names. Every order relation
adds the implication that inclusion of the larger element forces inclusion of the
smaller one. The construction uses no auxiliary variables.
-/

namespace StableMatching.PosetEncoding

variable {P : Type*} [Preorder P] [DecidableLE P] {n : Nat}

/-- The two-literal closure formula of an explicitly indexed finite poset. -/
def relationPairs (index : P ≃ Fin n) : List (Fin n × Fin n) :=
  ((List.finRange n).product (List.finRange n)).filter
    (fun p => index.symm p.1 ≤ index.symm p.2)

theorem mem_relationPairs (index : P ≃ Fin n) (p : Fin n × Fin n) :
    p ∈ relationPairs index ↔ index.symm p.1 ≤ index.symm p.2 := by
  rcases p with ⟨i, j⟩
  simp [relationPairs]

def cnf (index : P ≃ Fin n) : CNF where
  numVars := n
  clauses := (relationPairs index).map (fun p => [(p.2, false), (p.1, true)])

theorem clause_width (index : P ≃ Fin n) :
    ∀ clause ∈ (cnf index).clauses, clause.length ≤ 2 := by
  change ∀ clause ∈ (relationPairs index).map
    (fun p => [(p.2, false), (p.1, true)]), clause.length ≤ 2
  intro clause h
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
  simp

theorem satisfies_iff (index : P ≃ Fin n) (a : Fin n → Bool) :
    (cnf index).Satisfies a ↔
      ∀ x y : P, x ≤ y → a (index y) = true → a (index x) = true := by
  change (∀ clause ∈ (relationPairs index).map
      (fun p => [(p.2, false), (p.1, true)]),
      ∃ literal ∈ clause, a literal.1 = literal.2) ↔ _
  constructor
  · intro h x y hxy hy
    have hm : [(index y, false), (index x, true)] ∈
        (relationPairs index).map (fun p => [(p.2, false), (p.1, true)]) := by
      apply List.mem_map.mpr
      refine ⟨(index x, index y), ?_, rfl⟩
      simpa only [mem_relationPairs, Equiv.symm_apply_apply] using hxy
    obtain ⟨literal, hl, ha⟩ := h _ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · simp [hy] at ha
    · exact ha
  · intro h clause hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    have hxy : index.symm p.1 ≤ index.symm p.2 := by
      exact (mem_relationPairs index p).mp hp
    cases hb : a p.2 with
    | false => exact ⟨(p.2, false), by simp, hb⟩
    | true =>
      refine ⟨(p.1, true), by simp, ?_⟩
      simpa using h (index.symm p.1) (index.symm p.2) hxy (by simpa using hb)

/-- Satisfying assignments are exactly lower sets, with a unique code for each. -/
noncomputable def satisfyingEquivLowerSet (index : P ≃ Fin n) :
    {a : Fin n → Bool // (cnf index).Satisfies a} ≃ LowerSet P := by
  classical
  exact
    { toFun := fun a => ⟨{x | a.1 (index x) = true}, by
        intro x y hxy hx
        exact (satisfies_iff index a.1).mp a.2 y x hxy hx⟩
      invFun := fun s => ⟨fun i => decide (index.symm i ∈ s), by
        apply (satisfies_iff index _).mpr
        intro x y hxy hy
        have hy' : y ∈ s := by simpa using hy
        simpa using s.lower hxy hy'⟩
      left_inv := fun a => by
        apply Subtype.ext
        funext i
        cases h : a.1 i <;> simp
        · change ¬ (a.1 (index (index.symm i)) = true)
          simp [h]
        · change a.1 (index (index.symm i)) = true
          simpa using h
      right_inv := fun s => by
        apply LowerSet.ext
        ext x
        change (decide (index.symm (index x) ∈ s) = true) ↔ x ∈ s
        simp }

theorem satCount_eq_card_lowerSet (index : P ≃ Fin n) :
    (cnf index).satCount = Nat.card (LowerSet P) := by
  classical
  calc
    (cnf index).satCount =
        Fintype.card {a : Fin (cnf index).numVars → Bool // (cnf index).Satisfies a} := by
      exact (Fintype.card_subtype _).symm
    _ = Nat.card {a : Fin (cnf index).numVars → Bool // (cnf index).Satisfies a} :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (LowerSet P) := Nat.card_congr (satisfyingEquivLowerSet index)

@[simp] theorem numVars (index : P ≃ Fin n) : (cnf index).numVars = n := rfl

theorem clause_count (index : P ≃ Fin n) : (cnf index).clauses.length ≤ n * n := by
  change ((relationPairs index).map
    (fun p : Fin n × Fin n => ([(p.2, false), (p.1, true)] : List (Fin n × Bool)))).length ≤ n * n
  rw [List.length_map]
  calc
    (relationPairs index).length ≤
        ((List.finRange n).product (List.finRange n)).length := List.length_filter_le _ _
    _ = n * n := by
      change ((List.finRange n) ×ˢ (List.finRange n)).length = n * n
      rw [List.length_product, List.length_finRange]

theorem isThreeCNF (index : P ≃ Fin n) : (cnf index).IsThreeCNF := by
  intro clause h
  exact (clause_width index clause h).trans (by decide)

private theorem clause_injective : Function.Injective
    (fun p : Fin n × Fin n => ([(p.2, false), (p.1, true)] : List (Fin n × Bool))) := by
  intro p q h
  have hp : p.2 = q.2 ∧ p.1 = q.1 := by simpa using h
  exact Prod.ext hp.2 hp.1

theorem clauses_nodup (index : P ≃ Fin n) : (cnf index).clauses.Nodup := by
  change ((relationPairs index).map
    (fun p : Fin n × Fin n => ([(p.2, false), (p.1, true)] : List (Fin n × Bool)))).Nodup
  apply List.Nodup.map clause_injective
  exact ((List.nodup_finRange n).product (List.nodup_finRange n)).filter _

theorem diagonal_mem (index : P ≃ Fin n) (i : Fin n) :
    [(i, false), (i, true)] ∈ (cnf index).clauses := by
  change [(i, false), (i, true)] ∈ (relationPairs index).map
    (fun p : Fin n × Fin n => ([(p.2, false), (p.1, true)] : List (Fin n × Bool)))
  apply List.mem_map.mpr
  exact ⟨(i, i), (mem_relationPairs index (i, i)).mpr le_rfl, rfl⟩

theorem every_variable_occurs (index : P ≃ Fin n) (i : Fin n) :
    ∃ clause ∈ (cnf index).clauses, ∃ literal ∈ clause, literal.1 = i := by
  refine ⟨[(i, false), (i, true)], diagonal_mem index i, (i, true), ?_, rfl⟩
  exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem variables_le_clause_count (index : P ≃ Fin n) :
    n ≤ (cnf index).clauses.length := by
  change n ≤ ((relationPairs index).map
    (fun p : Fin n × Fin n => ([(p.2, false), (p.1, true)] : List (Fin n × Bool)))).length
  let diagonal : List (List (Fin n × Bool)) :=
    (List.finRange n).map (fun i => [(i, false), (i, true)])
  have hnodup : diagonal.Nodup := by
    apply List.Nodup.map _ (List.nodup_finRange n)
    intro i j h
    exact congrArg Prod.fst (clause_injective h : (i, i) = (j, j))
  have hsub : diagonal ⊆ (relationPairs index).map
      (fun p : Fin n × Fin n => ([(p.2, false), (p.1, true)] : List (Fin n × Bool))) := by
    intro clause h
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
    exact diagonal_mem index i
  simpa only [diagonal, List.length_map, List.length_finRange] using
    hnodup.length_le_of_subset hsub

end StableMatching.PosetEncoding
