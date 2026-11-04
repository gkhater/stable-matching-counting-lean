import StableMatching.ComputedCounting

/-! An executable application with two independent two-couple components.
Its two irreducibles are incomparable, so it also checks that the constructed
poset uses preference order rather than the numeric order of its indices. -/

namespace StableMatching.ComputedExample

open MathEconLib.Matching

def manScore (m : Fin 4) : Option (Fin 4) → Nat
  | none => 0
  | some w =>
      if m.val / 2 = w.val / 2 then (if m = w then 4 else 3)
      else if w.val % 2 = 0 then 2 else 1

def womanScore (w : Fin 4) : Option (Fin 4) → Nat
  | none => 0
  | some m =>
      if m.val / 2 = w.val / 2 then (if m = w then 3 else 4)
      else if m.val % 2 = 0 then 2 else 1

theorem manScore_injective : ∀ m : Fin 4, Function.Injective (manScore m) := by decide
theorem womanScore_injective : ∀ w : Fin 4, Function.Injective (womanScore w) := by decide

def market : MarriageMarket (Fin 4) (Fin 4) where
  prefM m := LinearOrder.lift' (manScore m) (manScore_injective m)
  prefW w := LinearOrder.lift' (womanScore w) (womanScore_injective w)

theorem completeLists :
    (∀ m w, market.ltM m none (some w)) ∧ (∀ w m, market.ltW w none (some m)) := by
  change (∀ m w, manScore m none < manScore m (some w)) ∧
    (∀ w m, womanScore w none < womanScore w (some m))
  decide

def decidableSatisfies (φ : CNF) (a : Fin φ.numVars → Bool) : Decidable (φ.Satisfies a) := by
  unfold CNF.Satisfies
  infer_instance

def evaluateCount (φ : CNF) : Nat :=
  letI := decidableSatisfies φ
  (Finset.univ.filter (fun a : Fin φ.numVars → Bool => φ.Satisfies a)).card

theorem evaluateCount_correct (φ : CNF) : evaluateCount φ = φ.satCount := by
  classical
  unfold evaluateCount CNF.satCount
  apply congrArg Finset.card
  ext a
  simp

theorem exact_count_from_computed_formula :
    evaluateCount (ComputedCounting.finiteCnf market) = Nat.card market.StableMatching :=
  (evaluateCount_correct _).trans (ComputedCounting.finiteCnf_correct market)

#guard (ComputedCounting.finiteCnf market).numVars == 2
#guard evaluateCount (ComputedCounting.finiteCnf market) == 4

end StableMatching.ComputedExample

#print axioms StableMatching.ComputedExample.exact_count_from_computed_formula
