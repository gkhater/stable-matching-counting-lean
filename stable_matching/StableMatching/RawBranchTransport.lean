import StableMatching.RawBranching

/-! The raw matrix primitives agree with the existing poset branching code. -/

namespace StableMatching.RawBranching

variable {P : Type*} [Preorder P] [DecidableLE P]
variable (matrix : Matrix) (label : P → Nat)
variable (hrel : ∀ x y, leTest matrix (label x) (label y) = decide (x ≤ y))

include hrel

theorem downSize_map (remaining : List P) (p : P) :
    downSize matrix (remaining.map label) (label p) = BranchTree.downSize remaining p := by
  simp only [downSize, BranchTree.downSize, List.filter_map, Function.comp_def,
    hrel, List.length_map]

theorem upSize_map (remaining : List P) (p : P) :
    upSize matrix (remaining.map label) (label p) = BranchTree.upSize remaining p := by
  simp only [upSize, BranchTree.upSize, List.filter_map, Function.comp_def,
    hrel, List.length_map]

theorem score_map (remaining : List P) (p : P) :
    score matrix (remaining.map label) (label p) = BranchTree.score remaining p := by
  rw [score, downSize_map matrix label hrel, upSize_map matrix label hrel]
  rfl

omit hrel in
theorem argmax_map {A B : Type*} (g : B → Nat) (e : A → B) (xs : List A) :
    (xs.map e).argmax g = (xs.argmax (g ∘ e)).map e := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.argmax_cons, List.argmax_cons, ih]
    cases h : xs.argmax (g ∘ e) with
    | none => rfl
    | some y =>
      by_cases hlt : g (e x) < g (e y) <;>
        simp only [Function.comp_def, hlt, ↓reduceIte, Option.map_some]

theorem pivot_map (remaining : List P) :
    pivot matrix (remaining.map label) =
      (remaining.argmax (BranchTree.score remaining)).map label := by
  unfold pivot
  rw [argmax_map]
  have hscore : score matrix (remaining.map label) ∘ label = BranchTree.score remaining := by
    funext p
    exact score_map matrix label hrel remaining p
  rw [hscore]

theorem includeResidual_map (hinj : Function.Injective label) (remaining : List P) (p : P) :
    includeResidual matrix (remaining.map label) (label p) =
      (BranchTree.includeResidual remaining p).map label := by
  unfold includeResidual BranchTree.includeResidual
  rw [List.filter_map]
  apply congrArg (List.map label)
  apply List.filter_congr
  intro x _
  dsimp only [Function.comp_def]
  rw [hrel x p]
  by_cases h : x ≤ p
  · simp [h]
  · have hne : x ≠ p := by intro heq; subst p; exact h le_rfl
    have hlne : label x ≠ label p := fun heq => hne (hinj heq)
    simp [h, hlne]

theorem excludeResidual_map (hinj : Function.Injective label) (remaining : List P) (p : P) :
    excludeResidual matrix (remaining.map label) (label p) =
      (BranchTree.excludeResidual remaining p).map label := by
  unfold excludeResidual BranchTree.excludeResidual
  rw [List.filter_map]
  apply congrArg (List.map label)
  apply List.filter_congr
  intro x _
  dsimp only [Function.comp_def]
  rw [hrel p x]
  by_cases h : p ≤ x
  · simp [h]
  · have hne : x ≠ p := by intro heq; subst p; exact h le_rfl
    have hlne : label x ≠ label p := fun heq => hne (hinj heq)
    simp [h, hlne]

end StableMatching.RawBranching
