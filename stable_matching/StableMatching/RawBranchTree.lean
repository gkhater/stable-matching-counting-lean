import StableMatching.RawBranchTransport

/-! A total matrix-based branching tree and its agreement with the poset tree. -/

namespace StableMatching.RawBranching

def build (matrix : Matrix) (cutoff : Nat) (remaining : List Nat) : BranchTree.Tree Nat := by
  by_cases hstop : remaining.length ≤ cutoff
  · exact .leaf remaining
  · cases hp : pivot matrix remaining with
    | none => exact .leaf remaining
    | some p =>
      exact .node p (build matrix cutoff (includeResidual matrix remaining p))
        (build matrix cutoff (excludeResidual matrix remaining p))
termination_by remaining.length
decreasing_by
  · exact include_length_lt matrix remaining p
      (List.argmax_mem (by simpa only [pivot, Option.mem_def] using hp))
  · exact exclude_length_lt matrix remaining p
      (List.argmax_mem (by simpa only [pivot, Option.mem_def] using hp))

def mapTree {P Q : Type*} (f : P → Q) : BranchTree.Tree P → BranchTree.Tree Q
  | .leaf r => .leaf (r.map f)
  | .node p l r => .node (f p) (mapTree f l) (mapTree f r)

def nodes {P : Type*} : BranchTree.Tree P → Nat
  | .leaf _ => 1
  | .node _ l r => 1 + nodes l + nodes r

theorem nodes_pos {P : Type*} (tree : BranchTree.Tree P) : 0 < nodes tree := by
  cases tree <;> simp [nodes]

theorem nodes_add_one {P : Type*} (tree : BranchTree.Tree P) :
    nodes tree + 1 = 2 * tree.leaves.length := by
  induction tree with
  | leaf r => simp [nodes, BranchTree.Tree.leaves]
  | node p l r ihl ihr =>
    simp only [nodes, BranchTree.Tree.leaves, List.length_append]
    omega

theorem mapTree_leaves {P Q : Type*} (f : P → Q) (tree : BranchTree.Tree P) :
    (mapTree f tree).leaves = tree.leaves.map (List.map f) := by
  induction tree <;> simp [mapTree, BranchTree.Tree.leaves, *]

theorem mapTree_height {P Q : Type*} (f : P → Q) (tree : BranchTree.Tree P) :
    (mapTree f tree).height = tree.height := by
  induction tree <;> simp [mapTree, BranchTree.Tree.height, *]

theorem mapTree_nodes {P Q : Type*} (f : P → Q) (tree : BranchTree.Tree P) :
    nodes (mapTree f tree) = nodes tree := by
  induction tree <;> simp [mapTree, nodes, *]

theorem option_rec_apply_of_some {A B : Type*} {o : Option A}
    (onone : o = none → B) (osome : ∀ a, o = some a → B) (a : A) (h : o = some a) :
    (Option.rec (motive := fun x => o = x → B) onone osome o rfl) = osome a h := by
  cases h
  rfl

theorem eq_rec_const_apply {A B : Type*} {o a b : A}
    (h : a = b) (v : B) (q : o = b) :
    (Eq.rec (motive := fun x _ => o = x → B) (fun _ => v) h) q = v := by
  cases h
  rfl

private theorem eq_rec_subtype_apply {A B : Type*} {o a b : A} {R : B → Prop}
    (h : a = b) (v : B) (pr : o = a → R v) (q : o = b) :
    ((Eq.rec (motive := fun x _ => o = x → {v : B // R v})
      (fun e => ⟨v, pr e⟩) h) q).1 = v := by
  cases h
  rfl

theorem build_map {P : Type*} [Preorder P] [DecidableLE P]
    (matrix : Matrix) (label : P → Nat) (hinj : Function.Injective label)
    (hrel : ∀ x y, leTest matrix (label x) (label y) = decide (x ≤ y))
    (cutoff : Nat) (remaining : List P) :
    build matrix cutoff (remaining.map label) = mapTree label (BranchTree.build cutoff remaining).1 := by
  induction remaining using (measure List.length).wf.induction with
  | h remaining ih =>
    by_cases hstop : remaining.length ≤ cutoff
    · rw [build, BranchTree.build]
      simp only [List.length_map, hstop, ↓reduceDIte, mapTree]
    · cases hp : remaining.argmax (BranchTree.score remaining) with
      | none =>
        have hempty := List.argmax_eq_none.mp hp
        subst remaining
        simp at hstop
      | some p =>
        have hmem : p ∈ remaining := List.argmax_mem (by simpa only [Option.mem_def] using hp)
        have hraw : pivot matrix (remaining.map label) = some (label p) := by
          rw [pivot_map matrix label hrel, hp]
          rfl
        rw [build, BranchTree.build]
        simp only [List.length_map, hstop, ↓reduceDIte]
        rw [option_rec_apply_of_some _ _ _ hraw, option_rec_apply_of_some _ _ _ hp]
        rw [includeResidual_map matrix label hrel hinj, excludeResidual_map matrix label hrel hinj]
        rw [ih (BranchTree.includeResidual remaining p) (BranchTree.includeResidual_length_lt _ _ hmem),
          ih (BranchTree.excludeResidual remaining p) (BranchTree.excludeResidual_length_lt _ _ hmem)]
        simp only [eq_rec_const_apply, eq_rec_subtype_apply, mapTree]

end StableMatching.RawBranching
