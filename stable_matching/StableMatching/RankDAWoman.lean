import StableMatching.RankDACorrectness
import MathEconLib.Matching.Classical.Marriage.RankSymmetry

/-! The same costed DA implementation computes the woman-proposing endpoint
by exchanging rank tables, with agreement in the original participant labels. -/

namespace StableMatching.RankDA

open MathEconLib.Matching
open MathEconLib.Matching.MarriageMarket
open Groundwork

def womanOutput (input : Input) : Contracts :=
  (output (input.2, input.1)).map Prod.swap

theorem womanOutput_polyT : PolyT womanOutput := by
  have hp := output_polyT
  change PolyT (fun input : Input => (output (input.2, input.1)).map (fun p => (p.2, p.1)))
  fun_prop

theorem swapped_output_matching (p : RankInput) (m w : Fin p.men.length) :
    (w.val, m.val) ∈ output (p.women, p.men) ↔
      p.market.womanGaleShapleyComputable m = some w := by
  have hraw := output_matching p.swap (Fin.cast p.women_length.symm w)
    (Fin.cast p.women_length.symm m)
  have hcast := castFin_galeShapley_apply p.women_length p.swap.market w m
  have h : (w.val, m.val) ∈ output (p.women, p.men) ↔
      (castFin p.women_length p.swap.market).galeShapleyComputable w = some m :=
    hraw.trans hcast.symm
  rw [p.swap_market] at h
  exact h.trans (p.market.symm.galeShapleyComputable.inv w m).symm

theorem woman_output_matching (p : RankInput) (m w : Fin p.men.length) :
    (m.val, w.val) ∈ womanOutput (p.men, p.women) ↔
      p.market.womanGaleShapleyComputable m = some w := by
  constructor
  · intro h
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp h
    have hqeq : q = (w.val, m.val) := by
      have h := congrArg Prod.swap heq
      simpa using h
    subst q
    exact (swapped_output_matching p m w).mp hq
  · intro h
    exact List.mem_map.mpr ⟨(w.val, m.val), (swapped_output_matching p m w).mpr h, rfl⟩

end StableMatching.RankDA
