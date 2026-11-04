import StableMatching.LowerSetBranching
import Mathlib.Data.List.MinMax
import Init.Data.List.Nat.Basic
import Mathlib.Data.Fintype.Sets

/-!
# A concrete stopped ideal-counting tree

At each node the algorithm scans for a pivot maximizing the smaller inclusive
cone. It includes or excludes that pivot, removes the forced cone, and stops
at a supplied residual size. The tree and pivot selection are executable.
Exact count preservation follows from the proved lower-set branching bijection.
-/

namespace StableMatching.BranchTree

variable {P : Type*} [Preorder P] [DecidableLE P]

def includeResidual (remaining : List P) (pivot : P) : List P :=
  remaining.filter (fun x => decide (¬ x ≤ pivot))

def excludeResidual (remaining : List P) (pivot : P) : List P :=
  remaining.filter (fun x => decide (¬ pivot ≤ x))

def downSize (remaining : List P) (pivot : P) : Nat :=
  (remaining.filter (fun x => decide (x ≤ pivot))).length

def upSize (remaining : List P) (pivot : P) : Nat :=
  (remaining.filter (fun x => decide (pivot ≤ x))).length

def score (remaining : List P) (pivot : P) : Nat :=
  min (downSize remaining pivot) (upSize remaining pivot)

theorem includeResidual_length_lt (remaining : List P) (pivot : P) (hp : pivot ∈ remaining) :
    (includeResidual remaining pivot).length < remaining.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨pivot, hp, by simp⟩

theorem excludeResidual_length_lt (remaining : List P) (pivot : P) (hp : pivot ∈ remaining) :
    (excludeResidual remaining pivot).length < remaining.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨pivot, hp, by simp⟩

def includeOrderIso (remaining : List P) (pivot : P) :
    {x : {x : P // x ∈ remaining} // ¬ x.1 ≤ pivot} ≃o
      {x : P // x ∈ includeResidual remaining pivot} where
  toFun x := ⟨x.1.1, List.mem_filter.mpr ⟨x.1.2, by simpa using x.2⟩⟩
  invFun x := ⟨⟨x.1, (List.mem_filter.mp x.2).1⟩, by
    simpa using (List.mem_filter.mp x.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def excludeOrderIso (remaining : List P) (pivot : P) :
    {x : {x : P // x ∈ remaining} // ¬ pivot ≤ x.1} ≃o
      {x : P // x ∈ excludeResidual remaining pivot} where
  toFun x := ⟨x.1.1, List.mem_filter.mpr ⟨x.1.2, by simpa using x.2⟩⟩
  invFun x := ⟨⟨x.1, (List.mem_filter.mp x.2).1⟩, by
    simpa using (List.mem_filter.mp x.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

noncomputable def count (remaining : List P) : Nat :=
  Nat.card (LowerSet {x : P // x ∈ remaining})

theorem count_branch (remaining : List P) (pivot : P) (hp : pivot ∈ remaining) :
    count remaining = count (includeResidual remaining pivot) +
      count (excludeResidual remaining pivot) := by
  classical
  have h := LowerSetBranching.card_branch (⟨pivot, hp⟩ : {x : P // x ∈ remaining})
  exact h.trans (congrArg₂ Nat.add
    (Nat.card_congr (LowerSet.map (includeOrderIso remaining pivot)).toEquiv)
    (Nat.card_congr (LowerSet.map (excludeOrderIso remaining pivot)).toEquiv))

inductive Tree (P : Type*) where
  | leaf : List P → Tree P
  | node : P → Tree P → Tree P → Tree P

def Tree.leaves : Tree P → List (List P)
  | .leaf remaining => [remaining]
  | .node _ left right => left.leaves ++ right.leaves

def Tree.height : Tree P → Nat
  | .leaf _ => 0
  | .node _ left right => 1 + max left.height right.height

inductive Valid (cutoff : Nat) : List P → Tree P → Prop where
  | leaf (remaining : List P) : remaining.length ≤ cutoff → Valid cutoff remaining (.leaf remaining)
  | node {remaining : List P} {pivot : P} {left right : Tree P} :
      cutoff < remaining.length →
      pivot ∈ remaining →
      (∀ x ∈ remaining, score remaining x ≤ score remaining pivot) →
      Valid cutoff (includeResidual remaining pivot) left →
      Valid cutoff (excludeResidual remaining pivot) right →
      Valid cutoff remaining (.node pivot left right)

/-- The exact tree, accompanied by a proof that each branch and stopping rule is valid. -/
def build (cutoff : Nat) (remaining : List P) : {tree : Tree P // Valid cutoff remaining tree} := by
  by_cases hstop : remaining.length ≤ cutoff
  · exact ⟨.leaf remaining, .leaf remaining hstop⟩
  · cases hp : remaining.argmax (score remaining) with
    | none =>
        have hempty : remaining = [] := List.argmax_eq_none.mp hp
        subst remaining
        exact (hstop (Nat.zero_le cutoff)).elim
    | some pivot =>
        have harg : pivot ∈ remaining.argmax (score remaining) := by
          simpa only [Option.mem_def] using hp
        have hmem : pivot ∈ remaining := List.argmax_mem harg
        have hmax : ∀ x ∈ remaining, score remaining x ≤ score remaining pivot := by
          intro x hx
          exact List.le_of_mem_argmax hx harg
        let left := build cutoff (includeResidual remaining pivot)
        let right := build cutoff (excludeResidual remaining pivot)
        exact ⟨.node pivot left.1 right.1,
          .node (Nat.lt_of_not_ge hstop) hmem hmax left.2 right.2⟩
termination_by remaining.length
decreasing_by
  · exact includeResidual_length_lt remaining pivot hmem
  · exact excludeResidual_length_lt remaining pivot hmem

theorem Valid.count_preserving {cutoff : Nat} {remaining : List P} {tree : Tree P}
    (h : Valid cutoff remaining tree) :
    (tree.leaves.map count).sum = count remaining := by
  induction h with
  | leaf remaining _ => simp [Tree.leaves]
  | @node remaining pivot left right _ hp _ _ _ ihleft ihright =>
      simp only [Tree.leaves, List.map_append, List.sum_append]
      rw [ihleft, ihright]
      exact (count_branch remaining pivot hp).symm

theorem Valid.leaves_small {cutoff : Nat} {remaining : List P} {tree : Tree P}
    (h : Valid cutoff remaining tree) : ∀ leaf ∈ tree.leaves, leaf.length ≤ cutoff := by
  induction h with
  | leaf remaining hstop =>
      intro leaf hleaf
      simp only [Tree.leaves, List.mem_singleton] at hleaf
      subst leaf
      exact hstop
  | @node remaining pivot left right _ hp _ _ _ ihleft ihright =>
      intro leaf hleaf
      rcases List.mem_append.mp hleaf with hleft | hright
      · exact ihleft leaf hleft
      · exact ihright leaf hright

theorem Valid.height_le_length {cutoff : Nat} {remaining : List P} {tree : Tree P}
    (h : Valid cutoff remaining tree) : tree.height ≤ remaining.length := by
  induction h with
  | leaf remaining _ => exact Nat.zero_le _
  | @node remaining pivot left right _ hp _ _ _ ihleft ihright =>
      have hl := includeResidual_length_lt remaining pivot hp
      have hr := excludeResidual_length_lt remaining pivot hp
      change 1 + max left.height right.height ≤ remaining.length
      omega

omit [Preorder P] [DecidableLE P] in
theorem Tree.leaves_length_le_pow_height (tree : Tree P) :
    tree.leaves.length ≤ 2 ^ tree.height := by
  induction tree with
  | leaf remaining => simp [Tree.leaves, Tree.height]
  | node pivot left right ihleft ihright =>
      have hl : 2 ^ left.height ≤ 2 ^ max left.height right.height :=
        Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)
      have hr : 2 ^ right.height ≤ 2 ^ max left.height right.height :=
        Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)
      simp only [Tree.leaves, List.length_append, Tree.height, Nat.add_comm 1, pow_succ]
      omega

theorem includeResidual_length_add_downSize (remaining : List P) (pivot : P) :
    (includeResidual remaining pivot).length + downSize remaining pivot = remaining.length := by
  induction remaining with
  | nil => rfl
  | cons x remaining ih =>
      by_cases h : x ≤ pivot <;>
        simp [includeResidual, downSize, h] at ih ⊢ <;> omega

theorem excludeResidual_length_add_upSize (remaining : List P) (pivot : P) :
    (excludeResidual remaining pivot).length + upSize remaining pivot = remaining.length := by
  induction remaining with
  | nil => rfl
  | cons x remaining ih =>
      by_cases h : pivot ≤ x <;>
        simp [excludeResidual, upSize, h] at ih ⊢ <;> omega

theorem Valid.leaves_nodup {cutoff : Nat} {remaining : List P} {tree : Tree P}
    (h : Valid cutoff remaining tree) :
    remaining.Nodup → ∀ leaf ∈ tree.leaves, leaf.Nodup := by
  induction h with
  | leaf remaining _ =>
      intro hnodup leaf hleaf
      simp only [Tree.leaves, List.mem_singleton] at hleaf
      subst leaf
      exact hnodup
  | @node remaining pivot left right _ _ _ _ _ ihleft ihright =>
      intro hnodup leaf hleaf
      rcases List.mem_append.mp hleaf with hleft | hright
      · exact ihleft (hnodup.filter _) leaf hleft
      · exact ihright (hnodup.filter _) leaf hright

end StableMatching.BranchTree
