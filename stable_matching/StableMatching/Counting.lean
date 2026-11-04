import StableMatching.Transfer
import StableMatching.PosetEncoding
import StableMatching.LowerSetBranching
import MathEconLib.Matching.Classical.Marriage.Distributive
import MathEconLib.Matching.Classical.Marriage.OrderIdeals

/-!
# Exact counting from the existing stable-marriage lattice

The canonical poset consists of the intrinsic join-irreducible stable matchings.
Its ideal representation is proved in MathEconLib, rather than supplied as a
count-preservation hypothesis. This file proves a parsimonious two-CNF encoding.
The canonical indexing here is noncomputable; polynomial construction and the
participant-subexponential runtime require additional algorithmic results.
-/

namespace StableMatching.Counting

open MathEconLib.Matching

variable {P M W : Type*} [PartialOrder P] [Fintype P] [Fintype M] [Fintype W]

/-- Compatibility with the earlier finite-set ideal interface. -/
noncomputable def lowerSetEquivIdeal : LowerSet P ≃ {D : Finset P // IsIdeal D} := by
  classical
  exact
    { toFun := fun s => ⟨Finset.univ.filter (fun x => x ∈ s), by
        intro x y hxy hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact s.lower hxy hy⟩
      invFun := fun D => ⟨{x | x ∈ D.1}, by
        intro x y hyx hx
        exact D.2 y x hyx hx⟩
      left_inv := fun s => by
        apply LowerSet.ext
        ext x
        simp
      right_inv := fun D => by
        apply Subtype.ext
        ext x
        simp }

abbrev Irreducible (mkt : MarriageMarket M W) :=
  {μ : mkt.StableMatching // SupIrred μ}

noncomputable instance irreducibleFintype (mkt : MarriageMarket M W) :
    Fintype (Irreducible mkt) := Fintype.ofFinite _

/-- The formerly abstract ideal-correspondence interface has a concrete
instance for the intrinsic irreducible poset. -/
noncomputable def intrinsicCorrespondence (mkt : MarriageMarket M W) :
    RotationCorrespondence mkt (Irreducible mkt) where
  stableEquivIdeal := (MarriageMarket.StableMatching.lowerSetSupIrred mkt).toEquiv.trans
    lowerSetEquivIdeal

noncomputable def index (mkt : MarriageMarket M W) :
    Irreducible mkt ≃ Fin (Fintype.card (Irreducible mkt)) := Fintype.equivFin _

/-- A formula with a unique satisfying code for each actual stable matching. -/
noncomputable def cnf (mkt : MarriageMarket M W) : CNF := by
  classical
  exact PosetEncoding.cnf (index mkt)

theorem cnf_correct (mkt : MarriageMarket M W) :
    (cnf mkt).satCount = Fintype.card mkt.StableMatching := by
  classical
  exact (PosetEncoding.satCount_eq_card_lowerSet (index mkt)).trans
    ((Nat.card_congr (MarriageMarket.StableMatching.lowerSetSupIrred mkt).toEquiv).symm.trans
      Nat.card_eq_fintype_card)

theorem cnf_width (mkt : MarriageMarket M W) :
    ∀ clause ∈ (cnf mkt).clauses, clause.length ≤ 2 := by
  classical
  exact PosetEncoding.clause_width (index mkt)

theorem cnf_numVars (mkt : MarriageMarket M W) :
    (cnf mkt).numVars = Fintype.card (Irreducible mkt) := rfl

theorem cnf_numVars_le (mkt : MarriageMarket M W) :
    (cnf mkt).numVars ≤ Fintype.card M * (Fintype.card W + 1) := by
  rw [cnf_numVars]
  simpa only [Nat.card_eq_fintype_card] using
    MarriageMarket.StableMatching.card_supIrred_le mkt

theorem cnf_clause_count (mkt : MarriageMarket M W) :
    (cnf mkt).clauses.length ≤ Fintype.card (Irreducible mkt) ^ 2 := by
  classical
  simpa only [cnf, pow_two] using PosetEncoding.clause_count (index mkt)

theorem stable_count_branch (mkt : MarriageMarket M W) (p : Irreducible mkt) :
    Nat.card mkt.StableMatching =
      Nat.card (LowerSet {x : Irreducible mkt // ¬ x ≤ p}) +
      Nat.card (LowerSet {x : Irreducible mkt // ¬ p ≤ x}) := by
  exact (Nat.card_congr (MarriageMarket.StableMatching.lowerSetSupIrred mkt).toEquiv).trans
    (LowerSetBranching.card_branch p)

end StableMatching.Counting
