import StableMatching.RawChainCutCorrect
import StableMatching.CNFNormalization
import MainResults
import ToTuring.Lib.List3
import ToTuring.Lib.List1b
import ToTuring.Lib.Nat1b

/-!
# Raw preparation for the Anthropic counter

The program receives a unary variable fuel as well as the raw natural-index
clauses. The fuel makes occurrence completion polynomial in the encoded input
size. The equality lemmas identify its output with the typed CNF preparation.
-/

namespace StableMatching.RawSATInput

open Groundwork RawChainCut

def padFour (raw : RawCNF) : RawCNF :=
  (raw.1 + 4,
    raw.2 ++ (List.range 4).map (fun j => [(raw.1 + j, false)]))

def withOccurrence (varsFuel : List Unit) (raw : RawCNF) : RawCNF :=
  (raw.1,
    raw.2 ++ (List.range varsFuel.length).map
      (fun i => [(i, true), (i, false)]))

def eraseDuplicate (raw : RawCNF) : RawCNF :=
  (raw.1, raw.2.dedup)

def prepare (varsFuel : List Unit) (raw : RawCNF) : RawCNF :=
  eraseDuplicate (withOccurrence
    (varsFuel ++ List.replicate 4 ()) (padFour raw))

@[fun_prop] theorem padFour_polyT {α : Type} [Enc α]
    {raw : α → RawCNF} (hraw : PolyT raw) :
    PolyT (fun x => padFour (raw x)) := by
  unfold padFour
  fun_prop

@[fun_prop] theorem withOccurrence_polyT {α : Type} [Enc α]
    {varsFuel : α → List Unit} {raw : α → RawCNF}
    (hf : PolyT varsFuel) (hraw : PolyT raw) :
    PolyT (fun x => withOccurrence (varsFuel x) (raw x)) := by
  have hrange : PolyT (fun x => List.range (varsFuel x).length) :=
    Groundwork.PolyT.range (Groundwork.Unary.of_length hf)
  unfold withOccurrence
  fun_prop

@[fun_prop] theorem eraseDuplicate_polyT {α : Type} [Enc α]
    {raw : α → RawCNF} (hraw : PolyT raw) :
    PolyT (fun x => eraseDuplicate (raw x)) := by
  unfold eraseDuplicate
  fun_prop

theorem prepare_polyT :
    PolyT (fun p : List Unit × RawCNF => prepare p.1 p.2) := by
  have hpad : PolyT (fun p : List Unit × RawCNF => padFour p.2) :=
    padFour_polyT (by fun_prop)
  have hfuel : PolyT (fun p : List Unit × RawCNF =>
      p.1 ++ List.replicate 4 ()) := by fun_prop
  have hocc : PolyT (fun p : List Unit × RawCNF =>
      withOccurrence (p.1 ++ List.replicate 4 ()) (padFour p.2)) :=
    withOccurrence_polyT hfuel hpad
  exact eraseDuplicate_polyT hocc

private def literalToRaw {n : ℕ} (lit : Fin n × Bool) : Nat × Bool :=
  (lit.1.val, lit.2)

private theorem literalToRaw_injective {n : ℕ} :
    Function.Injective (literalToRaw (n := n)) := by
  intro a b h
  change (a.1.val, a.2) = (b.1.val, b.2) at h
  have hi : a.1.val = b.1.val := congrArg (fun p : Nat × Bool => p.1) h
  have hb : a.2 = b.2 := congrArg (fun p : Nat × Bool => p.2) h
  exact Prod.ext (Fin.ext hi) hb

private theorem clauseToRaw_injective {n : ℕ} :
    Function.Injective (fun C : List (Fin n × Bool) => C.map literalToRaw) :=
  List.map_injective_iff.mpr literalToRaw_injective

theorem padFour_serialize (φ : StableMatching.CNF) :
    padFour (RawChainCut.serialize φ) = RawChainCut.serialize φ.padFour := by
  cases φ with
  | mk n clauses =>
      simp [padFour, RawChainCut.serialize, StableMatching.CNF.padFour,
        StableMatching.CNF.castFourLiteral, literalToRaw,
        List.map_map, Function.comp_def]
      rw [RawChainCut.range_eq_map_finRange]
      simp only [List.map_map, Function.comp_def]

theorem withOccurrence_serialize (φ : StableMatching.CNF)
    (varsFuel : List Unit) (hlen : varsFuel.length = φ.numVars) :
    withOccurrence varsFuel (RawChainCut.serialize φ) =
      RawChainCut.serialize φ.withOccurrenceTautologies := by
  cases φ with
  | mk n clauses =>
      simp only [withOccurrence, RawChainCut.serialize,
        StableMatching.CNF.withOccurrenceTautologies, Prod.mk.injEq,
        List.map_append, List.map_map, hlen, List.length_replicate]
      constructor
      · trivial
      · rw [RawChainCut.range_eq_map_finRange]
        simp only [List.map_map, Function.comp_def]
        simp only [List.map_cons, List.map_nil]

theorem eraseDuplicate_serialize (φ : StableMatching.CNF) :
    eraseDuplicate (RawChainCut.serialize φ) =
      RawChainCut.serialize φ.eraseDuplicateClauses := by
  cases φ with
  | mk n clauses =>
      classical
      simp only [eraseDuplicate, RawChainCut.serialize,
        StableMatching.CNF.eraseDuplicateClauses, Prod.mk.injEq]
      constructor
      · trivial
      · exact List.dedup_map_of_injective
          (clauseToRaw_injective (n := n)) clauses

theorem prepare_serialize (φ : StableMatching.CNF)
    (varsFuel : List Unit) (hlen : varsFuel.length = φ.numVars) :
    prepare varsFuel (RawChainCut.serialize φ) =
      RawChainCut.serialize φ.prepare := by
  unfold prepare StableMatching.CNF.prepare
  rw [padFour_serialize,
    withOccurrence_serialize φ.padFour
      (varsFuel ++ List.replicate 4 ()) (by simp [hlen, StableMatching.CNF.padFour]),
    eraseDuplicate_serialize]

/-- The slot bit positions are generated from a unary upper bound. On valid
inputs the `take` does not truncate; on arbitrary raw inputs it keeps the
program polynomial in the supplied fuel. -/
def slotIndices (varsFuel : List Unit) (n : Nat) : List Nat :=
  (List.range (2 * varsFuel.length + 1)).take (Nat.log2 (2 * n) + 1)

theorem slotIndices_eq_range (varsFuel : List Unit) (n : Nat)
    (hlen : varsFuel.length = n) :
    slotIndices varsFuel n = List.range (Nat.log2 (2 * n) + 1) := by
  unfold slotIndices
  rw [hlen, List.take_range]
  have hlog := Nat.log2_le_self (2 * n)
  rw [Nat.min_eq_left (by omega : Nat.log2 (2 * n) + 1 ≤ 2 * n + 1)]

theorem slotIndices_polyT :
    PolyT (fun p : List Unit × Nat => slotIndices p.1 p.2) := by
  have hf : PolyT (fun p : List Unit × Nat => p.1) := by fun_prop
  have hbase : Unary (fun p : List Unit × Nat => 2 * p.1.length + 1) :=
    ((Groundwork.Unary.const 2).mul (Groundwork.Unary.of_length hf)).add
      (Groundwork.Unary.const 1)
  have hrange : PolyT (fun p : List Unit × Nat =>
      List.range (2 * p.1.length + 1)) := Groundwork.PolyT.range hbase
  unfold slotIndices
  fun_prop

@[fun_prop] theorem slotIndices_polyT_apply {α : Type} [Enc α]
    {varsFuel : α → List Unit} {n : α → Nat}
    (hf : PolyT varsFuel) (hn : PolyT n) :
    PolyT (fun x => slotIndices (varsFuel x) (n x)) :=
  slotIndices_polyT.comp (Groundwork.PolyT.prodMk hf hn)

def slotRaw (lit : Option (Nat × Bool)) : Nat :=
  (lit.map fun l => 2 * l.1 + 1 + l.2.toNat).getD 0

@[fun_prop] theorem slotRaw_polyT {α : Type} [Enc α]
    {lit : α → Option (Nat × Bool)} (hlit : PolyT lit) :
    PolyT (fun x => slotRaw (lit x)) := by
  unfold slotRaw
  fun_prop

theorem slotRaw_map_getElem? {n : Nat}
    (clause : List (Fin n × Bool)) (j : Nat) :
    slotRaw ((clause.map literalToRaw)[j]?) = MainResults.slot clause[j]? := by
  simp only [List.getElem?_map]
  cases clause[j]? with
  | none => rfl
  | some lit => rfl

/-- The exact bit word expected by `MainResults.CountsWithin`, using only raw
natural-index clauses and two unary fuels. -/
def encodeInput (widthFuel varsFuel : List Unit) (raw : RawCNF) : List Bool :=
  widthFuel.map (fun _ => true) ++
    (false :: (varsFuel.map (fun _ => true) ++
      (false :: raw.2.flatMap (fun clause =>
        (List.range widthFuel.length).flatMap (fun j =>
          (slotIndices varsFuel raw.1).map
            (slotRaw clause[j]?).testBit)))))

theorem encodeInput_serialize (φ : StableMatching.CNF)
    (widthFuel varsFuel : List Unit)
    (hvars : varsFuel.length = φ.numVars) :
    encodeInput widthFuel varsFuel (RawChainCut.serialize φ) =
      MainResults.encInput widthFuel.length φ.clauses := by
  cases φ with
  | mk n clauses =>
      simp only [encodeInput, RawChainCut.serialize, MainResults.encInput,
        MainResults.encClauses, List.length_map, hvars,
        slotIndices_eq_range, List.map_const', List.flatMap_map]
      apply congrArg (fun body : List Bool =>
        List.replicate widthFuel.length true ++
          (false :: (List.replicate n true ++ (false :: body))))
      apply List.flatMap_congr
      intro clause hclause
      apply List.flatMap_congr
      intro j hj
      apply List.map_congr_left
      intro bit hbit
      change (slotRaw ((clause.map literalToRaw)[j]?)).testBit bit =
        (MainResults.slot clause[j]?).testBit bit
      rw [slotRaw_map_getElem?]

theorem encodeInput_prepared (φ : StableMatching.CNF)
    (widthFuel varsFuel : List Unit) (hvars : varsFuel.length = φ.numVars) :
    encodeInput widthFuel (varsFuel ++ List.replicate 4 ())
      (prepare varsFuel (RawChainCut.serialize φ)) =
      MainResults.encInput widthFuel.length φ.prepare.clauses := by
  rw [prepare_serialize φ varsFuel hvars]
  exact encodeInput_serialize φ.prepare widthFuel _
    (by simp [hvars, StableMatching.CNF.prepare_numVars])

theorem encodeInput_polyT :
    PolyT (fun p : (List Unit × List Unit) × RawCNF =>
      encodeInput p.1.1 p.1.2 p.2) := by
  have hwidth : PolyT (fun p : (List Unit × List Unit) × RawCNF =>
      List.range p.1.1.length) :=
    Groundwork.PolyT.range (Groundwork.Unary.of_length (by fun_prop))
  have hslots : PolyT (fun p : (List Unit × List Unit) × RawCNF =>
      slotIndices p.1.2 p.2.1) :=
    slotIndices_polyT.comp (Groundwork.PolyT.prodMk
      (by fun_prop) (by fun_prop))
  have hbody : PolyT (fun p : (List Unit × List Unit) × RawCNF =>
      p.2.2.flatMap (fun clause =>
        (List.range p.1.1.length).flatMap (fun j =>
          (slotIndices p.1.2 p.2.1).map
            (slotRaw clause[j]?).testBit))) := by
    fun_prop
  unfold encodeInput
  fun_prop

end StableMatching.RawSATInput
