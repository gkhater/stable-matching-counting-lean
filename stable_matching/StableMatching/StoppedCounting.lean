import StableMatching.ComputedCounting
import StableMatching.ResidualEncoding
import StableMatching.ThinBranching

/-!
# The actual stable-matching stopped reduction

The market supplies the finite DA-generated poset. The algorithm constructs
the stopped tree and every leaf formula. All count, variable, width and query
bounds below are proved for that construction, without a rotation-correspondence
or KOW-encoding input.
-/

namespace StableMatching.StoppedCounting

open MathEconLib.Matching MathEconLib.Order

def pullbackThinChains {P Q R C : Type*} [PartialOrder P] [PartialOrder Q]
    (t : ThinChains P R C) (e : Q ≃o P) : ThinChains Q R C where
  row x := t.row (e x)
  col x := t.col (e x)
  label_injective := by
    intro x y h
    exact e.injective (t.label_injective h)
  row_comparable x y h := by
    rcases t.row_comparable (e x) (e y) h with hxy | hyx
    · exact Or.inl (e.le_iff_le.mp hxy)
    · exact Or.inr (e.le_iff_le.mp hyx)
  col_comparable x y h := by
    rcases t.col_comparable (e x) (e y) h with hxy | hyx
    · exact Or.inl (e.le_iff_le.mp hxy)
    · exact Or.inr (e.le_iff_le.mp hyx)

variable {m n : Nat}

def indexSize (mkt : MarriageMarket (Fin m) (Fin n)) : Nat :=
  (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length

@[instance_reducible]
def indexOrder (mkt : MarriageMarket (Fin m) (Fin n)) : PartialOrder (Fin (indexSize mkt)) :=
  mkt.computedIrreducibleOrder (List.finRange m) (List.finRange n)

@[instance_reducible]
def indexDecidableLE (mkt : MarriageMarket (Fin m) (Fin n)) :
    @DecidableLE (Fin (indexSize mkt)) (indexOrder mkt).toLE :=
  mkt.computedIrreducibleDecidableLE (List.finRange m) (List.finRange n)

/-- The formulas actually constructed by DA, maximal-cone branching and leaf encoding. -/
def reduce (mkt : MarriageMarket (Fin m) (Fin n)) (cutoff : Nat) : List CNF :=
  letI : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  letI : Preorder (Fin (indexSize mkt)) := (indexOrder mkt).toPreorder
  letI := indexDecidableLE mkt
  ResidualEncoding.reduce cutoff (List.finRange (indexSize mkt))

theorem reduce_correct (mkt : MarriageMarket (Fin m) (Fin n)) (cutoff : Nat) :
    ((reduce mkt cutoff).map CNF.satCount).sum = Nat.card mkt.StableMatching := by
  let : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  let : Preorder (Fin (indexSize mkt)) := (indexOrder mkt).toPreorder
  let := indexDecidableLE mkt
  let e : Fin (indexSize mkt) ≃o {μ : mkt.StableMatching // SupIrred μ} :=
    mkt.computedIrreducibleOrderIso (List.finRange m) (List.finRange n)
    (fun _ => List.mem_finRange _) (fun _ => List.mem_finRange _)
  have hcount := ResidualEncoding.reduce_correct cutoff (List.finRange (indexSize mkt))
    (List.nodup_finRange _) (fun _ => List.mem_finRange _)
  exact hcount.trans
    (Nat.card_congr ((MarriageMarket.StableMatching.lowerSetSupIrred mkt).toEquiv.trans
      (LowerSet.map e.symm).toEquiv)).symm

theorem reduce_variable_bound (mkt : MarriageMarket (Fin m) (Fin n)) (cutoff : Nat) :
    ∀ φ ∈ reduce mkt cutoff, φ.numVars ≤ cutoff := by
  let : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  let : Preorder (Fin (indexSize mkt)) := (indexOrder mkt).toPreorder
  let := indexDecidableLE mkt
  exact ResidualEncoding.reduce_variable_bound cutoff (List.finRange (indexSize mkt))

theorem reduce_width (mkt : MarriageMarket (Fin m) (Fin n)) (cutoff : Nat) :
    ∀ φ ∈ reduce mkt cutoff, ∀ clause ∈ φ.clauses, clause.length ≤ 2 := by
  let : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  let : Preorder (Fin (indexSize mkt)) := (indexOrder mkt).toPreorder
  let := indexDecidableLE mkt
  exact ResidualEncoding.reduce_width cutoff (List.finRange (indexSize mkt))

/-- Used in correctness proofs only: the computed numeric poset inherits the
proved thin chains of intrinsic irreducibles. The algorithm never consults it. -/
noncomputable def thinChains (mkt : MarriageMarket (Fin m) (Fin n)) :
    @ThinChains (Fin (indexSize mkt)) (Fin m) (Fin n) (indexOrder mkt) := by
  letI : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  letI : PartialOrder (Fin (indexSize mkt)) := indexOrder mkt
  let e : Fin (indexSize mkt) ≃o {μ : mkt.StableMatching // SupIrred μ} :=
    mkt.computedIrreducibleOrderIso (List.finRange m) (List.finRange n)
    (fun _ => List.mem_finRange _) (fun _ => List.mem_finRange _)
  exact pullbackThinChains (MarriageMarket.StableMatching.irreducibleThinChains mkt) e

theorem reduce_query_bound (mkt : MarriageMarket (Fin m) (Fin n))
    (cutoff H : Nat) (hcutoff : 0 < cutoff) (harea : 0 < m * n)
    (hH : 1 + (8 * m * n : ℝ) / (cutoff : ℝ) ≤ H) :
    (reduce mkt cutoff).length ≤ 2 ^ H := by
  let : LE (Fin (indexSize mkt)) := (indexOrder mkt).toLE
  let : Preorder (Fin (indexSize mkt)) := (indexOrder mkt).toPreorder
  let : PartialOrder (Fin (indexSize mkt)) := indexOrder mkt
  let := indexDecidableLE mkt
  exact ThinBranching.reduce_query_bound (thinChains mkt) cutoff H hcutoff
    (by simpa only [Fintype.card_fin] using harea)
    (by simpa only [Fintype.card_fin] using hH)
    (List.finRange (indexSize mkt)) (List.nodup_finRange _)

end StableMatching.StoppedCounting
