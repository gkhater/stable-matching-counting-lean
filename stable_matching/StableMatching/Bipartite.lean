import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Filter

/-! A height-two order associated to a finite bipartite graph, and its ideal/independent-set bijection. -/

namespace StableMatching

variable {L R : Type*} [Fintype L] [Fintype R]

structure BipartiteGraph (L R : Type*) where
  edge : L → R → Prop

namespace BipartiteGraph

variable (G : BipartiteGraph L R)

def heightTwoLE : L ⊕ R → L ⊕ R → Prop
  | .inl l, .inl l' => l = l'
  | .inl l, .inr r => G.edge l r
  | .inr _, .inl _ => False
  | .inr r, .inr r' => r = r'

def heightTwoOrder : PartialOrder (L ⊕ R) where
  le := G.heightTwoLE
  le_refl := by
    intro x
    cases x <;> simp [heightTwoLE]
  le_trans := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;>
      simp_all [heightTwoLE]
  le_antisymm := by
    intro x y hxy hyx
    cases x <;> cases y <;>
      simp_all [heightTwoLE]

/-- Downward closure in the height-two poset, written at the edges. -/
def IsDown (D : Finset (L ⊕ R)) : Prop :=
  ∀ l r, G.edge l r → Sum.inr r ∈ D → Sum.inl l ∈ D

def IsIndependent (I : Finset (L ⊕ R)) : Prop :=
  ∀ l r, G.edge l r → ¬ (Sum.inl l ∈ I ∧ Sum.inr r ∈ I)

noncomputable def edgeCount : ℕ := by
  classical
  exact (Finset.univ.filter fun p : L × R => G.edge p.1 p.2).card

/-- The order-theoretic meaning of `IsDown`. -/
theorem isDown_iff_orderIdeal (D : Finset (L ⊕ R)) :
    G.IsDown D ↔
      (letI := G.heightTwoOrder
       ∀ x y : L ⊕ R, x ≤ y → y ∈ D → x ∈ D) := by
  constructor
  · intro h x y hxy hy
    cases x with
    | inl l =>
      cases y with
      | inl l' =>
        have heq : l = l' := hxy
        simpa [heq] using hy
      | inr r => exact h l r hxy hy
    | inr r =>
      cases y with
      | inl l => exact False.elim hxy
      | inr r' =>
        have heq : r = r' := hxy
        simpa [heq] using hy
  · intro h l r he hr
    exact h (Sum.inl l) (Sum.inr r) he hr

/-- Complement the left side and retain the right side. -/
noncomputable def toggleLeft (G : BipartiteGraph L R)
    (S : Finset (L ⊕ R)) : Finset (L ⊕ R) := by
  classical
  exact Finset.univ.filter fun x =>
    match x with
    | .inl l => Sum.inl l ∉ S
    | .inr r => Sum.inr r ∈ S

@[simp] theorem inl_mem_toggleLeft (S : Finset (L ⊕ R)) (l : L) :
    Sum.inl l ∈ G.toggleLeft S ↔ Sum.inl l ∉ S := by
  classical
  simp [toggleLeft]

@[simp] theorem inr_mem_toggleLeft (S : Finset (L ⊕ R)) (r : R) :
    Sum.inr r ∈ G.toggleLeft S ↔ Sum.inr r ∈ S := by
  classical
  simp [toggleLeft]

theorem toggleLeft_involutive (S : Finset (L ⊕ R)) :
    G.toggleLeft (G.toggleLeft S) = S := by
  ext x
  cases x <;> simp

theorem independent_toggleLeft_of_down {D : Finset (L ⊕ R)}
    (h : G.IsDown D) : G.IsIndependent (G.toggleLeft D) := by
  intro l r he hboth
  exact (G.inl_mem_toggleLeft D l).mp hboth.1 (h l r he
    ((G.inr_mem_toggleLeft D r).mp hboth.2))

theorem down_toggleLeft_of_independent {I : Finset (L ⊕ R)}
    (h : G.IsIndependent I) : G.IsDown (G.toggleLeft I) := by
  intro l r he hr
  apply (G.inl_mem_toggleLeft I l).mpr
  intro hl
  exact h l r he ⟨hl, (G.inr_mem_toggleLeft I r).mp hr⟩

/-- The explicit, involutive bijection. -/
noncomputable def downEquivIndependent :
    {D : Finset (L ⊕ R) // G.IsDown D} ≃
      {I : Finset (L ⊕ R) // G.IsIndependent I} where
  toFun D := ⟨G.toggleLeft D.1, G.independent_toggleLeft_of_down D.2⟩
  invFun I := ⟨G.toggleLeft I.1, G.down_toggleLeft_of_independent I.2⟩
  left_inv D := by
    apply Subtype.ext
    exact G.toggleLeft_involutive D.1
  right_inv I := by
    apply Subtype.ext
    exact G.toggleLeft_involutive I.1

noncomputable instance downFintype :
    Fintype {D : Finset (L ⊕ R) // G.IsDown D} := by
  classical
  infer_instance

noncomputable instance independentFintype :
    Fintype {I : Finset (L ⊕ R) // G.IsIndependent I} := by
  classical
  infer_instance

theorem card_down_eq_independent :
    Fintype.card {D : Finset (L ⊕ R) // G.IsDown D} =
      Fintype.card {I : Finset (L ⊕ R) // G.IsIndependent I} := by
  classical
  exact Fintype.card_congr G.downEquivIndependent

theorem finset_card_down_eq_independent :
    (Finset.univ : Finset {D : Finset (L ⊕ R) // G.IsDown D}).card =
      (Finset.univ : Finset {I : Finset (L ⊕ R) // G.IsIndependent I}).card := by
  classical
  simpa using G.card_down_eq_independent

end BipartiteGraph
end StableMatching

#print axioms StableMatching.BipartiteGraph.card_down_eq_independent
#print axioms StableMatching.BipartiteGraph.finset_card_down_eq_independent
#print axioms StableMatching.BipartiteGraph.isDown_iff_orderIdeal
#print axioms StableMatching.BipartiteGraph.downEquivIndependent
