import StableMatching.RankRows
import MathEconLib.Matching.Classical.Marriage.ComputedBlocks

/-! Uniformly costed numeric chain blocks for the computed irreducible poset. -/

namespace StableMatching.RankDA

open Groundwork
open MathEconLib.Matching.MarriageMarket

/-- The actual numeric row blocks, with the block length supplied as data. -/
def rowBlocksCode (D : Nat) (input : Input) (remaining : List Nat) :
    List (List Nat) :=
  (List.range input.1.length).flatMap (fun m =>
    MathEconLib.ListChunks.chunks D (sortedRowCode input remaining m))

private theorem foldl_splitLengths (sizes : List Nat) (xs : List Nat)
    (acc : List (List Nat)) :
    (sizes.foldl (fun (s : List Nat × List (List Nat)) (c : Nat) =>
      (s.1.drop c, s.1.take c :: s.2)) (xs, acc)).2 =
      (sizes.splitLengths xs).reverse ++ acc := by
  induction sizes generalizing xs acc with
  | nil => rfl
  | cons c sizes ih =>
      rw [List.foldl_cons, ih, List.splitLengths_cons, List.reverse_cons,
        List.append_assoc]
      simp

private theorem splitLengthsNat_polyT {α : Type} [Enc α]
    {sizes : α → List Nat} {xs : α → List Nat}
    (hsizes : PolyT sizes) (hxs : PolyT xs) :
    PolyT (fun p => (sizes p).splitLengths (xs p)) := by
  have h : PolyT (fun p => (sizes p).foldl
      (fun (s : List Nat × List (List Nat)) (c : Nat) =>
        (s.1.drop c, s.1.take c :: s.2)) (xs p, [])) := by
    refine Groundwork.PolyT.foldl_add
      (g := fun _ (s : List Nat × List (List Nat)) (c : Nat) =>
        (s.1.drop c, s.1.take c :: s.2))
      hsizes (by fun_prop) (by fun_prop)
      ⟨fun _ => 4, Groundwork.PB.const 4, ?_⟩
    rintro p ⟨v, a⟩ c -
    have h₁ := Groundwork.len_append (v.take c) (v.drop c)
    rw [List.take_append_drop] at h₁
    simp only [Groundwork.len_pair, Groundwork.len_cons]
    omega
  exact h.snd.reverse.congr fun p => by rw [foldl_splitLengths]; simp

private theorem chunksNat_polyT :
    PolyT (fun p : Nat × List Nat => MathEconLib.ListChunks.chunks p.1 p.2) := by
  have hcount : PolyT (fun p : Nat × List Nat => p.2.length / p.1 + 1) := by
    fun_prop
  have hbound : Groundwork.Unary
      (fun p : Nat × List Nat => p.2.length + 1) :=
    Groundwork.Unary.add (Groundwork.Unary.of_length (by fun_prop))
      (Groundwork.Unary.const 1)
  have hcountUnary : Groundwork.Unary
      (fun p : Nat × List Nat => p.2.length / p.1 + 1) :=
    Groundwork.Unary.of_le hbound hcount (by
      intro p
      have h := Nat.div_le_self p.2.length p.1
      omega)
  have hsizes : PolyT (fun p : Nat × List Nat =>
      List.replicate (p.2.length / p.1 + 1) p.1) := by
    have h : PolyT (fun p : Nat × List Nat =>
        (List.replicate (p.2.length / p.1 + 1) ()).map (fun _ => p.1)) := by
      exact Groundwork.PolyT.map (by fun_prop) hcountUnary
    exact h.congr fun p => by simp
  have hsplit : PolyT (fun p : Nat × List Nat =>
      (List.replicate (p.2.length / p.1 + 1) p.1).splitLengths p.2) :=
    splitLengthsNat_polyT hsizes (by fun_prop)
  unfold MathEconLib.ListChunks.chunks
  fun_prop

theorem rowBlocksCode_polyT :
    PolyT (fun p : Nat × Input × List Nat =>
      rowBlocksCode p.1 p.2.1 p.2.2) := by
  have hrange : PolyT (fun p : Nat × Input × List Nat =>
      List.range p.2.1.1.length) :=
    Groundwork.PolyT.range (Groundwork.Unary.of_length (by fun_prop))
  have hsort : PolyT (fun p : (Nat × Input × List Nat) × Nat =>
      sortedRowCode p.1.2.1 p.1.2.2 p.2) := by
    change PolyT ((fun t : Input × List Nat × Nat =>
      sortedRowCode t.1 t.2.1 t.2.2) ∘
      (fun p : (Nat × Input × List Nat) × Nat =>
        (p.1.2.1, p.1.2.2, p.2)))
    exact Groundwork.PolyT.comp
      (f := fun t : Input × List Nat × Nat =>
        sortedRowCode t.1 t.2.1 t.2.2)
      (g := fun p : (Nat × Input × List Nat) × Nat =>
        (p.1.2.1, p.1.2.2, p.2)) sortedRowCode_polyT (by fun_prop)
  have hinner : PolyT (fun p : (Nat × Input × List Nat) × Nat =>
      MathEconLib.ListChunks.chunks p.1.1
        (sortedRowCode p.1.2.1 p.1.2.2 p.2)) := by
    change PolyT ((fun t : Nat × List Nat =>
      MathEconLib.ListChunks.chunks t.1 t.2) ∘
      (fun p : (Nat × Input × List Nat) × Nat =>
        (p.1.1, sortedRowCode p.1.2.1 p.1.2.2 p.2)))
    exact Groundwork.PolyT.comp
      (f := fun t : Nat × List Nat => MathEconLib.ListChunks.chunks t.1 t.2)
      (g := fun p : (Nat × Input × List Nat) × Nat =>
        (p.1.1, sortedRowCode p.1.2.1 p.1.2.2 p.2)) chunksNat_polyT
      (Groundwork.PolyT.prodMk (by fun_prop) hsort)
  change PolyT (fun p : Nat × Input × List Nat =>
    (List.range p.2.1.1.length).flatMap (fun m =>
      MathEconLib.ListChunks.chunks p.1 (sortedRowCode p.2.1 p.2.2 m)))
  exact Groundwork.PolyT.flatMap hinner hrange

private theorem splitLengths_map {α β : Type} (f : α → β)
    (sizes : List Nat) (xs : List α) :
    sizes.splitLengths (xs.map f) =
      (sizes.splitLengths xs).map (List.map f) := by
  induction sizes generalizing xs with
  | nil => rfl
  | cons c sizes ih =>
      simp only [List.splitLengths_cons, List.map_cons, List.map_take]
      rw [← List.map_drop, ih]

private theorem chunks_map {α β : Type} (f : α → β)
    (D : Nat) (xs : List α) :
    MathEconLib.ListChunks.chunks D (xs.map f) =
      (MathEconLib.ListChunks.chunks D xs).map (List.map f) := by
  unfold MathEconLib.ListChunks.chunks
  simp only [List.length_map, splitLengths_map]
  generalize (List.replicate (xs.length / D + 1) D).splitLengths xs = blocks
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
      cases block <;> simp [ih]

theorem rowBlocksCode_correct (p : RankInput) (D : Nat)
    (remaining : List (Fin (p.market.computedIrreducibles
      (List.finRange p.men.length) (List.finRange p.men.length)).length)) :
    rowBlocksCode D (p.men, p.women) (remaining.map Fin.val) =
      (p.market.rowBlocks D remaining).map (List.map Fin.val) := by
  unfold rowBlocksCode MathEconLib.Matching.MarriageMarket.rowBlocks
  rw [range_eq_map_finRange]
  simp only [List.flatMap_map, List.map_flatMap]
  congr 1
  funext m
  rw [sortedRowCode_correct p remaining m, chunks_map]

end StableMatching.RankDA
