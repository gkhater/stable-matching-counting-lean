import StableMatching.BranchTree
import StableMatching.PosetEncoding
import Mathlib.Data.List.Nodup

/-!
# Executable CNF leaves of the stopped counting tree

Each residual list is indexed by its positions and encoded with the inherited
order, not the numeric order of those positions. Exact count preservation is
proved by composing the tree's branching bijections and the two-CNF encoding.
-/

namespace StableMatching.ResidualEncoding

variable {P : Type*} [Preorder P] [DecidableLE P]

@[instance_reducible]
def indexPreorder (remaining : List P) : Preorder (Fin remaining.length) where
  le i j := remaining.get i ≤ remaining.get j
  lt i j := remaining.get i ≤ remaining.get j ∧ ¬ remaining.get j ≤ remaining.get i
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans
  lt_iff_le_not_ge _ _ := Iff.rfl

@[instance_reducible]
def indexDecidableLE (remaining : List P) :
    @DecidableLE (Fin remaining.length) (indexPreorder remaining).toLE :=
  fun i j => inferInstanceAs (Decidable (remaining.get i ≤ remaining.get j))

def encode (remaining : List P) : CNF :=
  letI : LE (Fin remaining.length) := (indexPreorder remaining).toLE
  letI : Preorder (Fin remaining.length) := indexPreorder remaining
  letI := indexDecidableLE remaining
  PosetEncoding.cnf (Equiv.refl (Fin remaining.length))

def exhaustiveOrderIso (remaining : List P) (hall : ∀ x : P, x ∈ remaining) :
    {x : P // x ∈ remaining} ≃o P where
  toFun x := x.1
  invFun x := ⟨x, hall x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

omit [DecidableLE P] in
theorem count_eq_of_exhaustive (remaining : List P) (hall : ∀ x : P, x ∈ remaining) :
    BranchTree.count remaining = Nat.card (LowerSet P) :=
  Nat.card_congr (LowerSet.map (exhaustiveOrderIso remaining hall)).toEquiv

variable [DecidableEq P]

def indexOrderIso (remaining : List P) (hnodup : remaining.Nodup) :
    @OrderIso (Fin remaining.length) {x : P // x ∈ remaining}
      (indexPreorder remaining).toLE inferInstance where
  toFun i := ⟨remaining.get i, List.get_mem _ _⟩
  invFun x := ⟨remaining.idxOf x.1, List.idxOf_lt_length_of_mem x.2⟩
  left_inv i := by
    apply Fin.ext
    exact List.get_idxOf hnodup i
  right_inv x := by
    apply Subtype.ext
    exact List.getElem_idxOf _
  map_rel_iff' := Iff.rfl

theorem encode_correct (remaining : List P) (hnodup : remaining.Nodup) :
    (encode remaining).satCount = BranchTree.count remaining := by
  let : LE (Fin remaining.length) := (indexPreorder remaining).toLE
  let : Preorder (Fin remaining.length) := indexPreorder remaining
  let := indexDecidableLE remaining
  exact (PosetEncoding.satCount_eq_card_lowerSet (Equiv.refl (Fin remaining.length))).trans
    (Nat.card_congr (LowerSet.map (indexOrderIso remaining hnodup)).toEquiv)

omit [DecidableEq P] in
theorem encode_numVars (remaining : List P) : (encode remaining).numVars = remaining.length := rfl

omit [DecidableEq P] in
theorem encode_width (remaining : List P) :
    ∀ clause ∈ (encode remaining).clauses, clause.length ≤ 2 := by
  let : LE (Fin remaining.length) := (indexPreorder remaining).toLE
  let : Preorder (Fin remaining.length) := indexPreorder remaining
  let := indexDecidableLE remaining
  exact PosetEncoding.clause_width (Equiv.refl (Fin remaining.length))

theorem leaf_counts_correct {cutoff : Nat} {remaining : List P} {tree : BranchTree.Tree P}
    (h : BranchTree.Valid cutoff remaining tree) (hnodup : remaining.Nodup) :
    (tree.leaves.map (fun leaf => (encode leaf).satCount)).sum = BranchTree.count remaining := by
  calc
    (tree.leaves.map (fun leaf => (encode leaf).satCount)).sum =
        (tree.leaves.map BranchTree.count).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro leaf hleaf
      exact encode_correct leaf (h.leaves_nodup hnodup leaf hleaf)
    _ = BranchTree.count remaining := h.count_preserving

/-- The concrete list of oracle inputs constructed from a stopped tree. -/
def reduce (cutoff : Nat) (remaining : List P) : List CNF :=
  (BranchTree.build cutoff remaining).1.leaves.map encode

theorem reduce_correct (cutoff : Nat) (remaining : List P) (hnodup : remaining.Nodup)
    (hall : ∀ x : P, x ∈ remaining) :
    ((reduce cutoff remaining).map CNF.satCount).sum = Nat.card (LowerSet P) := by
  calc
    ((reduce cutoff remaining).map CNF.satCount).sum = BranchTree.count remaining := by
      simpa only [reduce, List.map_map, Function.comp_def] using
        leaf_counts_correct (BranchTree.build cutoff remaining).2 hnodup
    _ = Nat.card (LowerSet P) := count_eq_of_exhaustive remaining hall

omit [DecidableEq P] in
theorem reduce_variable_bound (cutoff : Nat) (remaining : List P) :
    ∀ φ ∈ reduce cutoff remaining, φ.numVars ≤ cutoff := by
  intro φ hφ
  obtain ⟨leaf, hleaf, rfl⟩ := List.mem_map.mp hφ
  exact (BranchTree.build cutoff remaining).2.leaves_small leaf hleaf

omit [DecidableEq P] in
theorem reduce_width (cutoff : Nat) (remaining : List P) :
    ∀ φ ∈ reduce cutoff remaining, ∀ clause ∈ φ.clauses, clause.length ≤ 2 := by
  intro φ hφ
  obtain ⟨leaf, _, rfl⟩ := List.mem_map.mp hφ
  exact encode_width leaf

end StableMatching.ResidualEncoding
