import StableMatching.RankDAWoman
import StableMatching.RankTruncationComplexity
import MathEconLib.Matching.Classical.Marriage.RankInputTruncation
import MathEconLib.Matching.Classical.Marriage.ThresholdComputation

/-! A costed threshold DA run, identified with the existing generator primitive. -/

namespace StableMatching.RankDA

open MathEconLib.Matching
open MathEconLib.Matching.MarriageMarket
open Groundwork
open RankInputComplexity

def thresholdOutput (input : Input) (m threshold : Nat) : Contracts :=
  womanOutput (truncateRankRows input.1 m threshold, input.2)

@[fun_prop] theorem thresholdOutput_polyT {α : Type} [Enc α]
    {input : α → Input} {m threshold : α → Nat}
    (hinput : PolyT input) (hm : PolyT m) (ht : PolyT threshold) :
    PolyT (fun x => thresholdOutput (input x) (m x) (threshold x)) := by
  have hw := womanOutput_polyT
  unfold thresholdOutput
  fun_prop

theorem threshold_output_matching (p : RankInput) (m threshold i w : Fin p.men.length) :
    (i.val, w.val) ∈ thresholdOutput (p.men, p.women) m.val threshold.val ↔
      p.market.thresholdDA m threshold i = some w := by
  let hlen := p.truncated_length m threshold
  have hraw := woman_output_matching (p.truncated m threshold)
    (Fin.cast hlen.symm i) (Fin.cast hlen.symm w)
  have hcast := castFin_womanGaleShapley_apply hlen (p.truncated m threshold).market i w
  have h : (i.val, w.val) ∈ thresholdOutput (p.men, p.women) m.val threshold.val ↔
      (castFin hlen (p.truncated m threshold).market).womanGaleShapleyComputable i = some w :=
    hraw.trans hcast.symm
  rw [p.truncated_market] at h
  exact h

end StableMatching.RankDA

#print axioms StableMatching.RankDA.thresholdOutput_polyT
#print axioms StableMatching.RankDA.threshold_output_matching
