import StableMatching.Bipartite
import StableMatching.Formula
import MathEconLib.Matching.Classical.Marriage.StableOrder
import Mathlib.Data.Finset.Image

/-! A conditional, statement-level transfer from C25a graphs to MathEconLib stable matchings. -/

namespace StableMatching

open MathEconLib.Matching

variable {L R P M W : Type*}
variable [Fintype L] [Fintype R] [Fintype P] [PartialOrder P]
variable [Fintype M] [Fintype W]

noncomputable instance stableMatchingFintype (mkt : MarriageMarket M W) :
    Fintype mkt.StableMatching := by
  classical
  have hinj : Function.Injective
      (fun μ : mkt.StableMatching => fun m : M => μ.matching m) := by
    intro μ ν h
    apply MarriageMarket.StableMatching.ext mkt
    apply PEquiv.ext
    intro m
    exact congrFun h m
  have : Finite mkt.StableMatching := Finite.of_injective _ hinj
  exact Fintype.ofFinite _

/-- Finite order ideal in the rotation poset. -/
def IsIdeal (D : Finset P) : Prop :=
  ∀ x y : P, x ≤ y → y ∈ D → x ∈ D

/-- Irving–Leather correspondence, taken as an explicit input. -/
structure RotationCorrespondence (mkt : MarriageMarket M W) (P : Type*)
    [Fintype P] [PartialOrder P] where
  stableEquivIdeal : mkt.StableMatching ≃ {D : Finset P // IsIdeal D}

/-- A poset realization; the order isomorphism is expressed without changing the
ambient order instance on the sum. The construction and its bounds are assumptions. -/
structure PosetRealization (G : BipartiteGraph L R) (P : Type*)
    [Fintype P] [PartialOrder P] (mkt : MarriageMarket M W) where
  vertexEquiv : P ≃ L ⊕ R
  order_iff : ∀ x y : P,
    x ≤ y ↔ G.heightTwoLE (vertexEquiv x) (vertexEquiv y)
  completeLists : (∀ m w, mkt.ltM m none (some w)) ∧
    (∀ w m, mkt.ltW w none (some m))
  agentBound : Fintype.card M + Fintype.card W ≤
    4 * Fintype.card (L ⊕ R)
  constructionSteps : ℕ
  linearConstruction : constructionSteps ≤
    4 * (Fintype.card (L ⊕ R) + G.edgeCount)

namespace PosetRealization

variable {G : BipartiteGraph L R} {mkt : MarriageMarket M W}

/-- Transport of ideals along the assumed poset isomorphism. -/
noncomputable def downEquiv (real : PosetRealization G P mkt) :
    {D : Finset P // IsIdeal D} ≃
      {D : Finset (L ⊕ R) // G.IsDown D} where
  toFun D := ⟨Equiv.finsetCongr real.vertexEquiv D.1, by
    intro l r he hr
    have hrP : real.vertexEquiv.symm (Sum.inr r) ∈ D.1 := by
      simpa using hr
    have hle : real.vertexEquiv.symm (Sum.inl l) ≤
        real.vertexEquiv.symm (Sum.inr r) := by
      apply (real.order_iff _ _).2
      simpa [BipartiteGraph.heightTwoLE] using he
    have hlP := D.2 _ _ hle hrP
    simpa using hlP⟩
  invFun D := ⟨Equiv.finsetCongr real.vertexEquiv.symm D.1, by
    intro x y hxy hy
    have hyG : real.vertexEquiv y ∈ D.1 := by
      simpa using hy
    have hle := (real.order_iff x y).1 hxy
    cases hx : real.vertexEquiv x with
    | inl l =>
      cases hy' : real.vertexEquiv y with
      | inl l' =>
        have heq : l = l' := by simpa [BipartiteGraph.heightTwoLE, hx, hy'] using hle
        have : real.vertexEquiv x = real.vertexEquiv y := by simp [hx, hy', heq]
        have : x = y := real.vertexEquiv.injective this
        simpa [this] using hy
      | inr r =>
        have he : G.edge l r := by simpa [BipartiteGraph.heightTwoLE, hx, hy'] using hle
        have hr : Sum.inr r ∈ D.1 := by simpa [hy'] using hyG
        have hl := D.2 l r he hr
        simpa [hx] using hl
    | inr r =>
      cases hy' : real.vertexEquiv y with
      | inl l =>
        have : False := by simpa [BipartiteGraph.heightTwoLE, hx, hy'] using hle
        exact False.elim this
      | inr r' =>
        have heq : r = r' := by simpa [BipartiteGraph.heightTwoLE, hx, hy'] using hle
        have : real.vertexEquiv x = real.vertexEquiv y := by simp [hx, hy', heq]
        have : x = y := real.vertexEquiv.injective this
        simpa [this] using hy⟩
  left_inv D := by
    apply Subtype.ext
    exact (Equiv.finsetCongr real.vertexEquiv).left_inv D.1
  right_inv D := by
    apply Subtype.ext
    exact (Equiv.finsetCongr real.vertexEquiv).right_inv D.1

end PosetRealization

/-- C25a's whole graph construction is an explicit input; its four fixed
local identities are proved in `Gadgets.lean`. -/
structure SignedGraphReduction (L R : Type*) [Fintype L] [Fintype R] where
  source : CNF
  sourceThreeCNF : source.IsThreeCNF
  evenGraph : BipartiteGraph L R
  oddGraph : BipartiteGraph L R
  vertexBound : Fintype.card (L ⊕ R) ≤ 616 * source.clauses.length + 3
  unusedVariables : ℕ
  sign : ℤ
  sign_sq : sign * sign = 1
  signedIdentity : (source.satCount : ℤ) =
    (2 : ℤ) ^ unusedVariables * sign *
      ((Fintype.card {I : Finset (L ⊕ R) // evenGraph.IsIndependent I} : ℤ) -
       (Fintype.card {I : Finset (L ⊕ R) // oddGraph.IsIndependent I} : ℤ))

/-- Each realized instance counts the independent sets of its source graph. -/
theorem count_stable_eq_independent (G : BipartiteGraph L R)
    (mkt : MarriageMarket M W)
    (rot : RotationCorrespondence mkt P)
    (real : PosetRealization G P mkt) :
    Fintype.card mkt.StableMatching =
      Fintype.card {I : Finset (L ⊕ R) // G.IsIndependent I} := by
  classical
  calc
    Fintype.card mkt.StableMatching =
        Fintype.card {D : Finset P // IsIdeal D} :=
      Fintype.card_congr rot.stableEquivIdeal
    _ = Fintype.card {D : Finset (L ⊕ R) // G.IsDown D} :=
      Fintype.card_congr real.downEquiv
    _ = Fintype.card {I : Finset (L ⊕ R) // G.IsIndependent I} :=
      G.card_down_eq_independent

/-- The C25a vertex bound and the realization bound imply a linear agent bound. -/
theorem realized_agents_bound (red : SignedGraphReduction L R)
    (G : BipartiteGraph L R) (mkt : MarriageMarket M W)
    (real : PosetRealization G P mkt) :
    Fintype.card M + Fintype.card W ≤
      4 * (616 * red.source.clauses.length + 3) :=
  real.agentBound.trans (Nat.mul_le_mul_left 4 red.vertexBound)

/-- Conditional #3SAT-to-#SM signed identity, using MathEconLib's actual
`MarriageMarket.StableMatching` carrier on both complete-list instances. -/
theorem signed_stable_matching_identity (red : SignedGraphReduction L R)
    {PE PO : Type*} [Fintype PE] [PartialOrder PE]
    [Fintype PO] [PartialOrder PO]
    (evenMarket oddMarket : MarriageMarket M W)
    (evenRot : RotationCorrespondence evenMarket PE)
    (oddRot : RotationCorrespondence oddMarket PO)
    (evenReal : PosetRealization red.evenGraph PE evenMarket)
    (oddReal : PosetRealization red.oddGraph PO oddMarket) :
    (red.source.satCount : ℤ) =
      (2 : ℤ) ^ red.unusedVariables * red.sign *
        ((Fintype.card evenMarket.StableMatching : ℤ) -
         (Fintype.card oddMarket.StableMatching : ℤ)) := by
  rw [count_stable_eq_independent red.evenGraph evenMarket evenRot evenReal,
    count_stable_eq_independent red.oddGraph oddMarket oddRot oddReal]
  exact red.signedIdentity

end StableMatching

#print axioms StableMatching.count_stable_eq_independent
#print axioms StableMatching.realized_agents_bound
#print axioms StableMatching.signed_stable_matching_identity
#print axioms StableMatching.PosetRealization.downEquiv
