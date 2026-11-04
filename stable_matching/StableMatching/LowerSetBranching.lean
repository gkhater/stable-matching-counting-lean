import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Logic.Equiv.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Sets

/-!
# Exact branching for counting lower sets

At a pivot, excluding it removes its upper cone; including it removes its lower
cone. Both branches retain the induced order. The equivalences below prove that
this recursion neither loses nor duplicates any lower set.
-/

namespace StableMatching.LowerSetBranching

variable {P : Type*} [Preorder P]

def restrict (s : LowerSet P) (domain : Set P) : LowerSet domain :=
  ⟨{x | x.1 ∈ s}, fun _ _ hxy hx => s.lower hxy hx⟩

def extendExcluding (p : P) (s : LowerSet {x : P // ¬ p ≤ x}) : LowerSet P :=
  ⟨{x | ∃ hx : ¬ p ≤ x, (⟨x, hx⟩ : {x : P // ¬ p ≤ x}) ∈ s}, by
    intro x y hyx hx
    obtain ⟨hpx, hx⟩ := hx
    have hpy : ¬ p ≤ y := fun h => hpx (h.trans hyx)
    exact ⟨hpy, s.lower hyx hx⟩⟩

theorem not_mem_extendExcluding (p : P) (s : LowerSet {x : P // ¬ p ≤ x}) :
    p ∉ extendExcluding p s := by
  rintro ⟨hp, _⟩
  exact hp le_rfl

def extendIncluding (p : P) (s : LowerSet {x : P // ¬ x ≤ p}) : LowerSet P :=
  ⟨{x | x ≤ p ∨ ∃ hx : ¬ x ≤ p, (⟨x, hx⟩ : {x : P // ¬ x ≤ p}) ∈ s}, by
    intro x y hyx hx
    rcases hx with hxp | ⟨hxp, hx⟩
    · exact Or.inl (hyx.trans hxp)
    · by_cases hyp : y ≤ p
      · exact Or.inl hyp
      · exact Or.inr ⟨hyp, s.lower hyx hx⟩⟩

theorem mem_extendIncluding (p : P) (s : LowerSet {x : P // ¬ x ≤ p}) :
    p ∈ extendIncluding p s := Or.inl le_rfl

def excludingEquiv (p : P) :
    {s : LowerSet P // p ∉ s} ≃ LowerSet {x : P // ¬ p ≤ x} where
  toFun s := restrict s.1 {x | ¬ p ≤ x}
  invFun s := ⟨extendExcluding p s, not_mem_extendExcluding p s⟩
  left_inv s := by
    apply Subtype.ext
    apply LowerSet.ext
    ext x
    change (∃ hx : ¬ p ≤ x, x ∈ s.1) ↔ x ∈ s.1
    constructor
    · rintro ⟨_, hx⟩
      exact hx
    · intro hx
      exact ⟨fun hpx => s.2 (s.1.lower hpx hx), hx⟩
  right_inv s := by
    apply LowerSet.ext
    ext x
    change (∃ hx : ¬ p ≤ x.1, (⟨x.1, hx⟩ : {x : P // ¬ p ≤ x}) ∈ s) ↔ x ∈ s
    constructor
    · rintro ⟨_, hx⟩
      exact hx
    · intro hx
      exact ⟨x.2, hx⟩

def includingEquiv (p : P) :
    {s : LowerSet P // p ∈ s} ≃ LowerSet {x : P // ¬ x ≤ p} where
  toFun s := restrict s.1 {x | ¬ x ≤ p}
  invFun s := ⟨extendIncluding p s, mem_extendIncluding p s⟩
  left_inv s := by
    apply Subtype.ext
    apply LowerSet.ext
    ext x
    change (x ≤ p ∨ ∃ hx : ¬ x ≤ p, x ∈ s.1) ↔ x ∈ s.1
    constructor
    · rintro (hxp | ⟨_, hx⟩)
      · exact s.1.lower hxp s.2
      · exact hx
    · intro hx
      by_cases hxp : x ≤ p
      · exact Or.inl hxp
      · exact Or.inr ⟨hxp, hx⟩
  right_inv s := by
    apply LowerSet.ext
    ext x
    change (x.1 ≤ p ∨ ∃ hx : ¬ x.1 ≤ p, (⟨x.1, hx⟩ : {x : P // ¬ x ≤ p}) ∈ s) ↔ x ∈ s
    constructor
    · rintro (hxp | ⟨_, hx⟩)
      · exact (x.2 hxp).elim
      · exact hx
    · intro hx
      exact Or.inr ⟨x.2, hx⟩

/-- Each ideal has exactly one branch and exactly one residual ideal. -/
noncomputable def branchEquiv (p : P) :
    LowerSet P ≃ LowerSet {x : P // ¬ x ≤ p} ⊕ LowerSet {x : P // ¬ p ≤ x} := by
  classical
  exact (Equiv.sumCompl (fun s : LowerSet P => p ∈ s)).symm.trans
    (Equiv.sumCongr (includingEquiv p) (excludingEquiv p))

private theorem finite_lowerSet [Finite P] : Finite (LowerSet P) :=
  Finite.of_injective (fun s : LowerSet P => (s : Set P)) SetLike.coe_injective

theorem card_branch [Finite P] (p : P) :
    Nat.card (LowerSet P) =
      Nat.card (LowerSet {x : P // ¬ x ≤ p}) + Nat.card (LowerSet {x : P // ¬ p ≤ x}) := by
  have : Finite (LowerSet {x : P // ¬ x ≤ p}) := finite_lowerSet
  have : Finite (LowerSet {x : P // ¬ p ≤ x}) := finite_lowerSet
  exact (Nat.card_congr (branchEquiv p)).trans Nat.card_sum

end StableMatching.LowerSetBranching
