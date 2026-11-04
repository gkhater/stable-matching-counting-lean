import StableMatching.RankGeneratingPair
import MathEconLib.Matching.Classical.Marriage.ComputedRows

/-! Polynomial-time numeric rows ordered by their generating-partner ranks. -/

namespace StableMatching.RankDA

open Groundwork
open MathEconLib.Matching.MarriageMarket

def rowLeCode (input : Input) (m i j : Nat) : Bool :=
  decide (rankAt input.1 m (generatingPairCode input i).2 ≤
    rankAt input.1 m (generatingPairCode input j).2)

def rowCandidates (input : Input) (remaining : List Nat) (m : Nat) : List Nat :=
  remaining.filter (fun i => (generatingPairCode input i).1 == m)

def insertCode (input : Input) (m i : Nat) (xs : List Nat) : List Nat :=
  xs.takeWhile (fun j => !(rowLeCode input m i j)) ++
    i :: xs.dropWhile (fun j => !(rowLeCode input m i j))

def sortedRowCode (input : Input) (remaining : List Nat) (m : Nat) : List Nat :=
  (rowCandidates input remaining m).foldr (insertCode input m) []

@[fun_prop] theorem rowLeCode_polyT {α : Type} [Enc α]
    {input : α → Input} {m i j : α → Nat}
    (hinput : PolyT input) (hm : PolyT m) (hi : PolyT i) (hj : PolyT j) :
    PolyT (fun x => rowLeCode (input x) (m x) (i x) (j x)) := by
  have hgi := generatingPairCode_comp_polyT hinput hi
  have hgj := generatingPairCode_comp_polyT hinput hj
  unfold rowLeCode
  fun_prop

theorem rowCandidates_polyT {α : Type} [Enc α]
    {input : α → Input} {remaining : α → List Nat} {m : α → Nat}
    (hinput : PolyT input) (hr : PolyT remaining) (hm : PolyT m) :
    PolyT (fun x => rowCandidates (input x) (remaining x) (m x)) := by
  unfold rowCandidates
  have hgen : PolyT (fun p : α × Nat =>
      generatingPairCode (input p.1) p.2) :=
    generatingPairCode_comp_polyT (hinput.comp (by fun_prop)) (by fun_prop)
  fun_prop

@[fun_prop] theorem insertCode_polyT {α : Type} [Enc α]
    {input : α → Input} {m i : α → Nat} {xs : α → List Nat}
    (hinput : PolyT input) (hm : PolyT m) (hi : PolyT i) (hxs : PolyT xs) :
    PolyT (fun x => insertCode (input x) (m x) (i x) (xs x)) := by
  unfold insertCode
  fun_prop

theorem insertCode_eq_orderedInsert (input : Input) (m i : Nat) (xs : List Nat) :
    insertCode input m i xs =
      xs.orderedInsert (fun a b => rowLeCode input m a b = true) i := by
  rw [List.orderedInsert_eq_take_drop]
  simp [insertCode]

private theorem len_perm {α : Type} [Enc α] {xs ys : List α}
    (h : xs.Perm ys) : Groundwork.len xs = Groundwork.len ys := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [Groundwork.len_cons, ih]
  | swap a b xs => simp [Groundwork.len_cons]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem insertCode_len (input : Input) (m i : Nat) (xs : List Nat) :
    Groundwork.len (insertCode input m i xs) =
      Groundwork.len xs + Groundwork.len i + 2 := by
  rw [insertCode_eq_orderedInsert]
  have h := len_perm (List.perm_orderedInsert
    (fun a b => rowLeCode input m a b = true) i xs)
  rw [h, Groundwork.len_cons]
  omega

theorem sortedRowCode_polyT :
    PolyT (fun p : Input × List Nat × Nat =>
      sortedRowCode p.1 p.2.1 p.2.2) := by
  have hc : PolyT (fun p : Input × List Nat × Nat =>
      rowCandidates p.1 p.2.1 p.2.2) :=
    rowCandidates_polyT (by fun_prop) (by fun_prop) (by fun_prop)
  have hg : PolyT (fun t : (Input × List Nat × Nat) × Nat × List Nat =>
      insertCode t.1.1 t.1.2.2 t.2.1 t.2.2) :=
    insertCode_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  obtain ⟨s, hs, _, hlen⟩ := Groundwork.PolyT.len_bound hc
  have hB : ∃ b, Groundwork.PB b ∧
      ∀ (p : Input × List Nat × Nat) (acc : List Nat) (i : Nat),
        i ∈ rowCandidates p.1 p.2.1 p.2.2 →
        Groundwork.len (insertCode p.1 p.2.2 i acc) ≤
          Groundwork.len acc + b (Groundwork.len p) := by
    refine ⟨fun n => s n + 2, hs.add (Groundwork.PB.const 2), ?_⟩
    intro p acc i hi
    have hli := (Groundwork.len_le_of_mem hi).trans (hlen p)
    rw [insertCode_len]
    change Groundwork.len acc + Groundwork.len i + 2 ≤
      Groundwork.len acc + (s (Groundwork.len p) + 2)
    omega
  change PolyT (fun p : Input × List Nat × Nat =>
    (rowCandidates p.1 p.2.1 p.2.2).foldr
      (fun i acc => insertCode p.1 p.2.2 i acc) [])
  exact Groundwork.PolyT.foldr_add
    (l := fun p : Input × List Nat × Nat => rowCandidates p.1 p.2.1 p.2.2)
    (a := fun _ => ([] : List Nat))
    (g := fun p i acc => insertCode p.1 p.2.2 i acc)
    hc (Groundwork.PolyT.const []) hg hB

theorem rowLeCode_correct (p : RankInput) (m : Fin p.men.length)
    (i j : Fin (p.market.computedIrreducibles
      (List.finRange p.men.length) (List.finRange p.men.length)).length) :
    rowLeCode (p.men, p.women) m.val i.val j.val = true ↔
      p.market.rowLe (List.finRange p.men.length)
        (List.finRange p.men.length) m i j := by
  unfold rowLeCode MathEconLib.Matching.MarriageMarket.rowLe
  rw [generatingPairCode_correct p i, generatingPairCode_correct p j]
  simp only [decide_eq_true_eq]
  simpa [optionIndex] using (p.leM_iff m
    (some (p.market.generatingPair (List.finRange p.men.length)
      (List.finRange p.men.length) i).2)
    (some (p.market.generatingPair (List.finRange p.men.length)
      (List.finRange p.men.length) j).2)).symm

theorem rowCandidates_correct (p : RankInput)
    (remaining : List (Fin (p.market.computedIrreducibles
      (List.finRange p.men.length) (List.finRange p.men.length)).length))
    (m : Fin p.men.length) :
    rowCandidates (p.men, p.women) (remaining.map Fin.val) m.val =
      (remaining.filter (fun i => decide ((p.market.generatingPair
        (List.finRange p.men.length) (List.finRange p.men.length) i).1 = m))).map Fin.val := by
  unfold rowCandidates
  rw [List.filter_map]
  simp only [Function.comp_def]
  congr 1
  congr 1
  funext i
  rw [generatingPairCode_correct p i]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  exact Fin.ext_iff.symm

theorem sortedRowCode_eq_insertionSort (input : Input)
    (remaining : List Nat) (m : Nat) :
    sortedRowCode input remaining m =
      (rowCandidates input remaining m).insertionSort
        (fun i j => rowLeCode input m i j = true) := by
  unfold sortedRowCode List.insertionSort
  congr 1
  funext i acc
  exact insertCode_eq_orderedInsert input m i acc

theorem sortedRow_eq_insertionSort (p : RankInput)
    (remaining : List (Fin (p.market.computedIrreducibles
      (List.finRange p.men.length) (List.finRange p.men.length)).length))
    (m : Fin p.men.length) :
    p.market.sortedRow (List.finRange p.men.length)
      (List.finRange p.men.length) remaining m =
      (letI := p.market.rowLeDecidable (List.finRange p.men.length)
        (List.finRange p.men.length) m
      (remaining.filter (fun i => decide ((p.market.generatingPair
        (List.finRange p.men.length) (List.finRange p.men.length) i).1 = m))).insertionSort
        (p.market.rowLe (List.finRange p.men.length) (List.finRange p.men.length) m)) := by
  let r := p.market.rowLe (List.finRange p.men.length)
    (List.finRange p.men.length) m
  letI := p.market.rowLeDecidable (List.finRange p.men.length)
    (List.finRange p.men.length) m
  let : Std.Total r := ⟨fun i j => by
    letI := p.market.prefM m
    exact le_total _ _⟩
  let : IsTrans _ r := ⟨fun _ _ _ hij hjk => by
    letI := p.market.prefM m
    exact le_trans hij hjk⟩
  let row := remaining.filter (fun i => decide ((p.market.generatingPair
    (List.finRange p.men.length) (List.finRange p.men.length) i).1 = m))
  change row.mergeSort (fun i j => decide (r i j)) = row.insertionSort r
  refine List.Perm.eq_of_pairwise (le := r) ?_ ?_ ?_ ?_
  · intro a b ha hb hab hba
    have haRow : a ∈ row := (List.mergeSort_perm row _).mem_iff.mp ha
    have hbRow : b ∈ row := (List.perm_insertionSort r row).mem_iff.mp hb
    have haMan : (p.market.generatingPair (List.finRange p.men.length)
        (List.finRange p.men.length) a).1 = m := by
      exact (List.mem_filter.mp haRow).2 |> of_decide_eq_true
    have hbMan : (p.market.generatingPair (List.finRange p.men.length)
        (List.finRange p.men.length) b).1 = m := by
      exact (List.mem_filter.mp hbRow).2 |> of_decide_eq_true
    have hw : (p.market.generatingPair (List.finRange p.men.length)
        (List.finRange p.men.length) a).2 =
        (p.market.generatingPair (List.finRange p.men.length)
        (List.finRange p.men.length) b).2 := by
      letI := p.market.prefM m
      have hopt : some (p.market.generatingPair (List.finRange p.men.length)
          (List.finRange p.men.length) a).2 =
          some (p.market.generatingPair (List.finRange p.men.length)
          (List.finRange p.men.length) b).2 := le_antisymm hab hba
      exact Option.some.inj hopt
    apply p.market.generatingPair_injective (List.finRange p.men.length)
      (List.finRange p.men.length)
    exact Prod.ext (haMan.trans hbMan.symm) hw
  · exact p.market.sortedRow_pairwise_rowLe
      (List.finRange p.men.length) (List.finRange p.men.length) remaining m
  · exact List.pairwise_insertionSort r row
  · exact (List.mergeSort_perm row _).trans (List.perm_insertionSort r row).symm

theorem sortedRowCode_correct (p : RankInput)
    (remaining : List (Fin (p.market.computedIrreducibles
      (List.finRange p.men.length) (List.finRange p.men.length)).length))
    (m : Fin p.men.length) :
    sortedRowCode (p.men, p.women) (remaining.map Fin.val) m.val =
      (p.market.sortedRow (List.finRange p.men.length)
        (List.finRange p.men.length) remaining m).map Fin.val := by
  rw [sortedRowCode_eq_insertionSort, rowCandidates_correct,
    sortedRow_eq_insertionSort]
  letI := p.market.rowLeDecidable (List.finRange p.men.length)
    (List.finRange p.men.length) m
  symm
  apply List.map_insertionSort
    (r := p.market.rowLe (List.finRange p.men.length)
      (List.finRange p.men.length) m)
    (s := fun i j : Nat => rowLeCode (p.men, p.women) m.val i j = true)
  intro i _ j _
  exact (rowLeCode_correct p m i j).symm

end StableMatching.RankDA
