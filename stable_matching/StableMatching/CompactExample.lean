import StableMatching.CompactReduction
import StableMatching.ComputedExample

/-! Execute the compact reduction at two bit widths on an actual market. -/

namespace StableMatching.ComputedExample

def compactOneBit : List CNF := CompactReduction.reduce market 1 (by decide) 1
def compactTwoBits : List CNF := CompactReduction.reduce market 2 (by decide) 2

#guard compactOneBit.map CNF.numVars == [2]
#guard (compactOneBit.map evaluateCount).sum == 4
#guard compactTwoBits.map CNF.numVars == [4]
#guard (compactTwoBits.map evaluateCount).sum == 4

theorem compact_count_correct :
    (compactTwoBits.map CNF.satCount).sum = Nat.card market.StableMatching :=
  CompactReduction.reduce_correct market 2 (by decide) 2 (by decide)

end StableMatching.ComputedExample

#print axioms StableMatching.ComputedExample.compact_count_correct
