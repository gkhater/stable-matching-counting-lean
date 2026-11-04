import StableMatching.RankDA
import ToTuring.Poly.Words

/-! A Boolean input format and an actual polynomial-time rank-table reader.
The two unary headers give the side size and the bit width of each rank.
The body has the men's rows followed by the women's rows, with fixed-width
binary entries. -/

namespace StableMatching.RankInputCode

open Groundwork MathEconLib.Matching.MarriageMarket

def header (n : Nat) : List Bool := List.replicate n true ++ [false]
def ones (x : List Bool) : Nat := (x.takeWhile id).length
def rest (x : List Bool) : List Bool := (x.dropWhile id).tail

theorem ones_header (n : Nat) (x : List Bool) : ones (header n ++ x) = n := by
  induction n with
  | zero => simp [ones, header]
  | succ n ih => simp [ones, header, List.replicate_succ]

theorem rest_header (n : Nat) (x : List Bool) : rest (header n ++ x) = x := by
  induction n with
  | zero => simp [rest, header]
  | succ n ih => simp [rest, header, List.replicate_succ]

def writeRows (width : Nat) (rows : List (List Nat)) : List Bool :=
  rows.flatMap (fun row => row.flatMap (toWord width))

def readRows (count columns width : Nat) (body : List Bool) : List (List Nat) :=
  (chunks (List.replicate count (columns * width)) body).map
    (fun row => (chunks (List.replicate columns width) row).map ofWord)

def encode (p : RankInput) (width : Nat) : List Bool :=
  header p.men.length ++ header width ++ writeRows width (p.men ++ p.women)

def decode (x : List Bool) : RankDA.Input :=
  let n := ones x
  let width := ones (rest x)
  let rows := readRows (2 * n) (n + 1) width (rest (rest x))
  (rows.take n, rows.drop n)

theorem chunks_flatMap {A : Type} (f : A → List Bool) (width : Nat)
    (xs : List A) (h : ∀ a ∈ xs, (f a).length = width) :
    chunks (List.replicate xs.length width) (xs.flatMap f) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.length_cons, List.replicate_succ, List.flatMap_cons, chunks, List.map_cons]
    rw [← ha, List.take_left, List.drop_left]
    rw [ha]
    exact congrArg (List.cons (f a)) ht

theorem readRows_writeRows (rows : List (List Nat)) (columns width : Nat)
    (hr : ∀ row ∈ rows, row.length = columns)
    (hb : ∀ row ∈ rows, ∀ a ∈ row, a < 2 ^ width) :
    readRows rows.length columns width (writeRows width rows) = rows := by
  have hlen : ∀ row ∈ rows, (row.flatMap (toWord width)).length = columns * width := by
    intro row hrow
    simp only [List.length_flatMap, length_toWord, List.map_const', List.sum_replicate]
    rw [hr row hrow]
    simp only [smul_eq_mul]
  rw [readRows, writeRows, chunks_flatMap _ _ rows hlen, List.map_map]
  trans rows.map id
  · apply List.map_congr_left
    intro row hrow
    dsimp only [Function.comp_def, id_eq]
    rw [← hr row hrow, chunks_flatMap (toWord width) width row (by simp), List.map_map]
    trans row.map id
    · apply List.map_congr_left
      intro a ha
      exact ofWord_toWord (hb row hrow a ha)
    · exact List.map_id _
  · exact List.map_id _

theorem decode_encode (p : RankInput) (width : Nat)
    (hb : ∀ row ∈ p.men ++ p.women, ∀ a ∈ row, a < 2 ^ width) :
    decode (encode p width) = (p.men, p.women) := by
  have hlen : (p.men ++ p.women).length = 2 * p.men.length := by
    rw [List.length_append, p.women_length]
    omega
  have hr : ∀ row ∈ p.men ++ p.women, row.length = p.men.length + 1 := by
    intro row hrow
    rcases List.mem_append.mp hrow with hm | hw
    · exact p.men_row_length row hm
    · exact p.women_row_length row hw
  unfold decode encode
  rw [List.append_assoc, ones_header, rest_header, ones_header, rest_header]
  dsimp only
  rw [← hlen, readRows_writeRows _ _ _ hr hb]
  simp

@[fun_prop] theorem ones_polyT {A : Type} [Enc A] {x : A → List Bool} (hx : PolyT x) :
    PolyT (fun a => ones (x a)) := by unfold ones; fun_prop

@[fun_prop] theorem rest_polyT {A : Type} [Enc A] {x : A → List Bool} (hx : PolyT x) :
    PolyT (fun a => rest (x a)) := by unfold rest; fun_prop

theorem decode_polyT : PolyT decode := by
  have hn : Unary (fun x : List Bool => ones x) := Unary.of_length (by fun_prop)
  have hw : Unary (fun x : List Bool => ones (rest x)) :=
    Unary.of_length (by fun_prop)
  have hc : Unary (fun x : List Bool => 2 * ones x) := (Unary.const 2).mul hn
  have hcols : Unary (fun x : List Bool => ones x + 1) := hn.add (Unary.const 1)
  have houter : PolyT (fun x : List Bool =>
      List.replicate (2 * ones x) ((ones x + 1) * ones (rest x))) := by
    have hh : PolyT (fun x : List Bool => (List.replicate (2 * ones x) ()).map
        (fun _ => (ones x + 1) * ones (rest x))) :=
      PolyT.map (f := fun x (_ : Unit) => (ones x + 1) * ones (rest x)) (by fun_prop) hc
    exact hh.congr (by intro x; simp)
  have hinner : PolyT (fun x : List Bool => List.replicate (ones x + 1) (ones (rest x))) := by
    have hh : PolyT (fun x : List Bool => (List.replicate (ones x + 1) ()).map
        (fun _ => ones (rest x))) :=
      PolyT.map (f := fun x (_ : Unit) => ones (rest x)) (by fun_prop) hcols
    exact hh.congr (by intro x; simp)
  have hchunks : PolyT (fun x : List Bool => chunks
      (List.replicate (2 * ones x) ((ones x + 1) * ones (rest x))) (rest (rest x))) := by
    fun_prop
  have hreadrow : PolyT (fun p : List Bool × List Bool =>
      (chunks (List.replicate (ones p.1 + 1) (ones (rest p.1))) p.2).map ofWord) := by
    apply PolyT.map (f := fun (_ : List Bool × List Bool) bits => ofWord bits)
    · fun_prop
    · have hi := hinner.comp (g := fun p : List Bool × List Bool => p.1) (by fun_prop)
      fun_prop
  have hrows := PolyT.map (f := fun x row =>
    (chunks (List.replicate (ones x + 1) (ones (rest x))) row).map ofWord) hreadrow hchunks
  change PolyT (fun x : List Bool =>
    ((readRows (2 * ones x) (ones x + 1) (ones (rest x)) (rest (rest x))).take (ones x),
     (readRows (2 * ones x) (ones x + 1) (ones (rest x)) (rest (rest x))).drop (ones x)))
  unfold readRows
  exact PolyT.prodMk (PolyT.take (by fun_prop) hrows) (PolyT.drop (by fun_prop) hrows)

theorem encode_length (p : RankInput) (width : Nat) :
    (encode p width).length = p.men.length + width + 2 +
      2 * p.men.length * (p.men.length + 1) * width := by
  have hrow : ∀ row ∈ p.men ++ p.women,
      (row.flatMap (toWord width)).length = (p.men.length + 1) * width := by
    intro row hr
    have hlen : row.length = p.men.length + 1 := by
      rcases List.mem_append.mp hr with hm | hw
      · exact p.men_row_length row hm
      · exact p.women_row_length row hw
    simp [List.length_flatMap, hlen]
  have hbody : (writeRows width (p.men ++ p.women)).length =
      2 * p.men.length * ((p.men.length + 1) * width) := by
    unfold writeRows
    rw [List.length_flatMap, List.map_congr_left hrow]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_append, p.women_length]
    ring
  simp only [encode, header, List.length_append, List.length_replicate, List.length_singleton, hbody]
  ring

end StableMatching.RankInputCode
