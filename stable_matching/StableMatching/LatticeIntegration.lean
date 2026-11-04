import MathEconLib.Matching.Classical.Marriage.Distributive

/-! A checked application of the canonical stable-matching ideal representation. -/

namespace StableMatching.LatticeIntegration

open MathEconLib.Matching

@[instance_reducible] private def optionFinOneOrder : LinearOrder (Option (Fin 1)) := by
  let f : Option (Fin 1) → ℕ := fun o => if o.isSome then 1 else 0
  refine LinearOrder.lift' f ?_
  intro a b h
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b => simp [f] at h
  | some a =>
      cases b with
      | none => simp [f] at h
      | some b => exact congrArg some (Subsingleton.elim a b)

/-- A marriage market with one participant on each side and the usual option order. -/
def onePairMarket : MarriageMarket (Fin 1) (Fin 1) where
  prefM := fun _ => optionFinOneOrder
  prefW := fun _ => optionFinOneOrder

noncomputable instance : Fintype onePairMarket.StableMatching := by
  classical
  have hinj : Function.Injective
      (fun μ : onePairMarket.StableMatching => fun m : Fin 1 => μ.matching m) := by
    intro μ ν h
    apply MarriageMarket.StableMatching.ext onePairMarket
    apply PEquiv.ext
    intro m
    exact congrFun h m
  have : Finite onePairMarket.StableMatching := Finite.of_injective _ hinj
  exact Fintype.ofFinite _

noncomputable instance :
    Fintype (LowerSet {μ : onePairMarket.StableMatching // SupIrred μ}) := by
  classical
  exact Fintype.ofEquiv _
    (MarriageMarket.StableMatching.lowerSetSupIrred onePairMarket).toEquiv

/-- The canonical representation counts stable matchings by intrinsic ideals
in a concrete finite marriage market. -/
theorem onePair_stableCount_eq_idealCount :
    Fintype.card onePairMarket.StableMatching =
      Fintype.card (LowerSet
        {μ : onePairMarket.StableMatching // SupIrred μ}) := by
  classical
  let e := MarriageMarket.StableMatching.lowerSetSupIrred onePairMarket
  exact Fintype.card_congr e.toEquiv

end StableMatching.LatticeIntegration

#print axioms StableMatching.LatticeIntegration.onePair_stableCount_eq_idealCount
