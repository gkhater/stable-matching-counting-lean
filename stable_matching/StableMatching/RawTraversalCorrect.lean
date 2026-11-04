import StableMatching.RawTraversal
import StableMatching.RawBranchTree

/-! The DFS program visits exactly the nodes of the constructed branching tree. -/

namespace StableMatching.RawBranching

theorem build_leaf (matrix : Matrix) (cutoff : Nat) (r : List Nat)
    (h : r.length ≤ cutoff) : build matrix cutoff r = .leaf r := by
  rw [build]
  simp only [h, ↓reduceDIte]

theorem build_node (matrix : Matrix) (cutoff : Nat) (r : List Nat)
    (h : ¬ r.length ≤ cutoff) :
    build matrix cutoff r = .node ((pivot matrix r).getD 0)
      (build matrix cutoff (includeResidual matrix r ((pivot matrix r).getD 0)))
      (build matrix cutoff (excludeResidual matrix r ((pivot matrix r).getD 0))) := by
  have hne : r ≠ [] := by intro he; subst r; exact h (Nat.zero_le cutoff)
  have hp : pivot matrix r ≠ none := fun he => hne (List.argmax_eq_none.mp he)
  obtain ⟨p, he⟩ := Option.ne_none_iff_exists'.mp hp
  rw [build]
  simp only [h, ↓reduceDIte]
  rw [option_rec_apply_of_some _ _ _ he]
  simp only [eq_rec_const_apply, he, Option.getD_some]

end StableMatching.RawBranching

namespace StableMatching.RawTraversal

open Groundwork RawBranching

def work (matrix : Matrix) (cutoff : Nat) (pending : List (List Nat)) : Nat :=
  (pending.map (fun r => nodes (build matrix cutoff r))).sum

def results (matrix : Matrix) (cutoff : Nat) (pending : List (List Nat)) : List (List Nat) :=
  pending.flatMap (fun r => (build matrix cutoff r).leaves)

theorem work_nil (matrix : Matrix) (cutoff : Nat) : work matrix cutoff [] = 0 := rfl

theorem work_cons (matrix : Matrix) (cutoff : Nat) (r : List Nat) (rs : List (List Nat)) :
    work matrix cutoff (r :: rs) = nodes (build matrix cutoff r) + work matrix cutoff rs := rfl

theorem work_step_leaf (matrix : Matrix) (cutoff : Nat) (r : List Nat) (rs : List (List Nat))
    (h : r.length ≤ cutoff) : work matrix cutoff (r :: rs) = work matrix cutoff rs + 1 := by
  rw [work_cons, build_leaf matrix cutoff r h]
  simp only [nodes]
  omega

theorem work_step_node (matrix : Matrix) (cutoff : Nat) (r : List Nat) (rs : List (List Nat))
    (h : ¬ r.length ≤ cutoff) :
    work matrix cutoff (r :: rs) =
      work matrix cutoff (includeResidual matrix r ((pivot matrix r).getD 0) ::
        excludeResidual matrix r ((pivot matrix r).getD 0) :: rs) + 1 := by
  rw [work_cons, build_node matrix cutoff r h]
  simp only [nodes, work_cons]
  omega

theorem results_step_leaf (matrix : Matrix) (cutoff : Nat) (r : List Nat)
    (rs acc : List (List Nat)) (h : r.length ≤ cutoff) :
    acc.reverse ++ results matrix cutoff (r :: rs) =
      (r :: acc).reverse ++ results matrix cutoff rs := by
  simp [results, build_leaf matrix cutoff r h, BranchTree.Tree.leaves, List.append_assoc]

theorem results_step_node (matrix : Matrix) (cutoff : Nat) (r : List Nat)
    (rs : List (List Nat)) (h : ¬ r.length ≤ cutoff) :
    results matrix cutoff (r :: rs) =
      results matrix cutoff (includeResidual matrix r ((pivot matrix r).getD 0) ::
        excludeResidual matrix r ((pivot matrix r).getD 0) :: rs) := by
  simp [results, build_node matrix cutoff r h, BranchTree.Tree.leaves, List.append_assoc]

private theorem size_nil {A : Type} [HasSize A] : size ([] : List A) = 1 := rfl

private theorem size_cons {A : Type} [HasSize A] (x : A) (xs : List A) :
    size (x :: xs) = size x + size xs + 1 := by
  simp only [size_list, List.map_cons, List.sum_cons]
  omega

theorem size_sublist {A : Type} [HasSize A] {xs ys : List A} (h : xs.Sublist ys) :
    size xs ≤ size ys := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons x h ih => rw [size_cons]; omega
  | cons_cons x h ih => rw [size_cons, size_cons]; omega

theorem size_list_bound {A : Type} [HasSize A] (xs : List A) (bound : Nat)
    (h : ∀ x ∈ xs, size x ≤ bound) : size xs ≤ xs.length * (bound + 1) + 1 := by
  induction xs with
  | nil => simp only [size_nil, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    rw [size_cons, List.length_cons]
    nlinarith

def bound (matrix : Matrix) (cutoff : Nat) (initial : List Nat) (budget : Nat) : Nat :=
  size matrix + size cutoff + (budget + 1) * (size initial + 1) + 2

theorem state_size_bound (matrix : Matrix) (cutoff : Nat) (initial : List Nat)
    (pending acc : List (List Nat)) (budget : Nat)
    (hp : ∀ r ∈ pending, r.Sublist initial) (ha : ∀ r ∈ acc, r.Sublist initial)
    (hc : pending.length + acc.length ≤ budget + 1) :
    size (matrix, cutoff, pending, acc) ≤ bound matrix cutoff initial budget := by
  have hps := size_list_bound pending (size initial) (fun r hr => size_sublist (hp r hr))
  have has := size_list_bound acc (size initial) (fun r hr => size_sublist (ha r hr))
  simp only [size_prod, bound]
  nlinarith

theorem reaches (matrix : Matrix) (cutoff : Nat) (initial : List Nat) (budget : Nat)
    (pending acc : List (List Nat))
    (hp : ∀ r ∈ pending, r.Sublist initial) (ha : ∀ r ∈ acc, r.Sublist initial)
    (hc : work matrix cutoff pending + pending.length + acc.length ≤ budget + 1) :
    machine.Reaches (bound matrix cutoff initial budget)
      (acc.reverse ++ results matrix cutoff pending) (matrix, cutoff, pending, acc)
      (work matrix cutoff pending) := by
  induction pending using (measure (work matrix cutoff)).wf.induction generalizing acc with
  | h pending ih =>
    have hs := state_size_bound matrix cutoff initial pending acc budget hp ha (by omega)
    cases pending with
    | nil =>
      apply Stepped.Reaches.halt
      · simp [machine, out, results]
      · exact hs
    | cons r rs =>
      have hr := hp r (by simp)
      have hrs : ∀ q ∈ rs, q.Sublist initial := fun q hq => hp q (by simp [hq])
      by_cases hstop : r.length ≤ cutoff
      · have hw := work_step_leaf matrix cutoff r rs hstop
        rw [results_step_leaf matrix cutoff r rs acc hstop, hw]
        apply Stepped.Reaches.step
        · rfl
        · exact hs
        · have he : machine.step (matrix, cutoff, r :: rs, acc) =
              (matrix, cutoff, rs, r :: acc) := by simp [machine, step, hstop]
          rw [he]
          refine ih rs (by change work matrix cutoff rs < work matrix cutoff (r :: rs); omega)
            (r :: acc) hrs ?_ ?_
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hr
            · exact ha q hq
          · simp only [List.length_cons] at *
            omega
      · let l := includeResidual matrix r ((pivot matrix r).getD 0)
        let u := excludeResidual matrix r ((pivot matrix r).getD 0)
        have hl : l.Sublist initial := (List.filter_sublist).trans hr
        have hu : u.Sublist initial := (List.filter_sublist).trans hr
        have hw := work_step_node matrix cutoff r rs hstop
        change work matrix cutoff (r :: rs) = work matrix cutoff (l :: u :: rs) + 1 at hw
        rw [results_step_node matrix cutoff r rs hstop, hw]
        apply Stepped.Reaches.step
        · rfl
        · exact hs
        · have he : machine.step (matrix, cutoff, r :: rs, acc) =
              (matrix, cutoff, l :: u :: rs, acc) := by simp [machine, step, hstop, l, u]
          rw [he]
          refine ih (l :: u :: rs)
            (by change work matrix cutoff (l :: u :: rs) < work matrix cutoff (r :: rs); omega)
            acc ?_ ha ?_
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hl
            · rcases List.mem_cons.mp hq with rfl | hq
              · exact hu
              · exact hrs q hq
          · simp only [List.length_cons] at *
            omega

theorem machine_runs (matrix : Matrix) (cutoff : Nat) (initial : List Nat) :
    machine.Runs (matrix, cutoff, initial) (nodes (build matrix cutoff initial))
      (bound matrix cutoff initial (nodes (build matrix cutoff initial)))
      (build matrix cutoff initial).leaves := by
  have h := reaches matrix cutoff initial (nodes (build matrix cutoff initial)) [initial] []
    (by simp) (by simp) (by simp [work])
  simpa only [machine, Stepped.Runs, init, List.reverse_nil, results,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    work, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using h

end StableMatching.RawTraversal
