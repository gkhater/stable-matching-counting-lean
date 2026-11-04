import StableMatching.RankInputCode
import StableMatching.ScheduleComplexity
import StableMatching.RawChainCut

/-! Uniform, costed data for compact leaf encodings and their SAT serializer. -/

namespace StableMatching.UniformQueryParameters

open Groundwork

def n (code : List Bool) : Nat := (RankInputCode.decode code).1.length
def blockLength (code : List Bool) : Nat := ExecutableSchedule.blockLength (n code)
def bitWidth (code : List Bool) : Nat := ExecutableSchedule.bitWidth (n code)
def bitFuel (code : List Bool) : List Unit := List.replicate (bitWidth code) ()
def widthFuel (code : List Bool) : List Unit := bitFuel code ++ bitFuel code
def domain (code : List Bool) : List Nat := List.range (2 ^ bitWidth code)
def matrix (code : List Bool) : RawChainCut.Matrix := RankDA.orderRows (RankInputCode.decode code)

theorem n_unary : Unary n :=
  Unary.of_length RankInputCode.decode_polyT.fst

theorem blockLength_polyT : PolyT blockLength := ScheduleComplexity.blockLength_polyT n_unary
theorem bitWidth_polyT : PolyT bitWidth := ScheduleComplexity.bitWidth_polyT n_unary
theorem bitFuel_polyT : PolyT bitFuel := ScheduleComplexity.bitWidth_unary n_unary
theorem domain_polyT : PolyT domain := ScheduleComplexity.domain_polyT n_unary
theorem matrix_polyT : PolyT matrix := RankDA.orderRows_polyT.comp RankInputCode.decode_polyT

theorem widthFuel_polyT : PolyT widthFuel := by
  have h := bitFuel_polyT
  unfold widthFuel
  fun_prop

theorem bitFuel_length (code : List Bool) : (bitFuel code).length = bitWidth code :=
  List.length_replicate

theorem widthFuel_length (code : List Bool) :
    (widthFuel code).length = max (2 * bitWidth code) 2 := by
  have hp : 0 < bitWidth code := ExecutableSchedule.bitWidth_pos _
  simp only [widthFuel, List.length_append, bitFuel_length]
  omega

def varsFuel (code : List Bool) (blocks : RawChainCut.Blocks) : List Unit :=
  blocks.flatMap (fun _ => bitFuel code)

theorem varsFuel_polyT : PolyT (fun p : List Bool × RawChainCut.Blocks => varsFuel p.1 p.2) := by
  have hf := bitFuel_polyT.comp
    (g := fun p : (List Bool × RawChainCut.Blocks) × List Nat => p.1.1) (by fun_prop)
  unfold varsFuel
  exact PolyT.flatMap (f := fun p : List Bool × RawChainCut.Blocks =>
    fun (_ : List Nat) => bitFuel p.1) hf (PolyT.id' (α := List Bool × RawChainCut.Blocks)).snd

theorem varsFuel_length (code : List Bool) (blocks : RawChainCut.Blocks) :
    (varsFuel code blocks).length = blocks.length * bitWidth code := by
  simp [varsFuel, List.length_flatMap, bitFuel_length]

def encodeLeaf (p : List Bool × RawChainCut.Blocks) : RawChainCut.RawCNF :=
  RawChainCut.encode p.2 (matrix p.1) (domain p.1) (bitFuel p.1)

theorem encodeLeaf_polyT : PolyT encodeLeaf := by
  have hm := matrix_polyT
  have hd := domain_polyT
  have hf := bitFuel_polyT
  unfold encodeLeaf
  exact RawChainCut.encode_polyT.comp
    (g := fun p : List Bool × RawChainCut.Blocks =>
      ((p.2, matrix p.1), (domain p.1, bitFuel p.1))) (by fun_prop)

theorem varsFuel_length_eq_numVars (code : List Bool) (blocks : RawChainCut.Blocks) :
    (varsFuel code blocks).length = (encodeLeaf (code, blocks)).1 := by
  simp only [varsFuel_length, encodeLeaf, RawChainCut.encode, bitFuel_length]

end StableMatching.UniformQueryParameters
