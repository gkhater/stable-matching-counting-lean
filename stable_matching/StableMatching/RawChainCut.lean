import StableMatching.BlockPartition
import ToTuring.Lib.List3
import ToTuring.Lib.Unary

/-!
# Raw compact chain-cut clauses

The input lists carry the block positions, comparison matrix, explicit domain,
and unary bit width. Clause indices are natural numbers for the SAT serializer.
-/

namespace StableMatching.RawChainCut

open Groundwork

abbrev Blocks := List (List Nat)
abbrev Matrix := List (List Bool)
abbrev RawClause := List (Nat × Bool)
abbrev RawCNF := Nat × List RawClause

/-- A bit word is supplied by the verified binary-word routine. Reversing it
matches the high-bit-first order of `BinaryCSP.bitEquiv`. -/
def forbid (fuel : List Unit) (i v : Nat) : RawClause :=
  (List.range fuel.length).map fun k =>
    (i * fuel.length + k, !((toWord fuel.length v).reverse.getD k false))

def entries (blocks : Blocks) (domain : List Nat) : List (Nat × Nat) :=
  (List.range blocks.length).product domain

def matrixAt (matrix : Matrix) (x y : Nat) : Bool :=
  (matrix.getD x []).getD y false

/-- The cut on block `i` includes exactly the positions below `u`. -/
def compatible (blocks : Blocks) (matrix : Matrix)
    (i j u v : Nat) : Bool :=
  (List.range (blocks.getD i []).length).all fun r =>
    (List.range (blocks.getD j []).length).all fun t =>
      !(matrixAt matrix ((blocks.getD i []).getD r 0)
        ((blocks.getD j []).getD t 0) && decide (t < v) && !(decide (r < u)))

def invalidEntries (blocks : Blocks) (domain : List Nat) : List (Nat × Nat) :=
  (entries blocks domain).filter fun p => decide (p.2 > (blocks.getD p.1 []).length)

def badPairEntries (blocks : Blocks) (matrix : Matrix) (domain : List Nat) :
    List ((Nat × Nat) × (Nat × Nat)) :=
  ((entries blocks domain).product (entries blocks domain)).filter fun p =>
    !(compatible blocks matrix p.1.1 p.2.1 p.1.2 p.2.2)

/-- The plain-list CNF constructor; the domain and bit width are explicit
input lists, so the full enumeration has polynomial size in those inputs. -/
def encode (blocks : Blocks) (matrix : Matrix) (domain : List Nat)
    (fuel : List Unit) : RawCNF :=
  (blocks.length * fuel.length,
    (invalidEntries blocks domain).map (fun p => forbid fuel p.1 p.2) ++
    (badPairEntries blocks matrix domain).map (fun p =>
      forbid fuel p.1.1 p.1.2 ++ forbid fuel p.2.1 p.2.2))

@[fun_prop] theorem positions_polyT {α β : Type} [Enc α] [Enc β]
    {xs : α → List β} (hxs : PolyT xs) :
    PolyT (fun x => List.range (xs x).length) :=
  Groundwork.PolyT.range (Groundwork.Unary.of_length hxs)

@[fun_prop] theorem forbid_polyT {α : Type} [Enc α]
    {fuel : α → List Unit} {i v : α → Nat}
    (hf : PolyT fuel) (hi : PolyT i) (hv : PolyT v) :
    PolyT (fun x => forbid (fuel x) (i x) (v x)) := by
  have hword : PolyT (fun x => toWord (fuel x).length (v x)) :=
    Groundwork.PolyT.toWord' (Groundwork.Unary.of_length hf) hv
  have hrange : PolyT (fun x => List.range (fuel x).length) :=
    Groundwork.PolyT.range (Groundwork.Unary.of_length hf)
  have hword' : PolyT (fun p : α × Nat =>
      (toWord (fuel p.1).length (v p.1)).reverse) :=
    (Groundwork.PolyT.reverse hword).comp (by fun_prop)
  have hbody : PolyT (fun p : α × Nat =>
      (i p.1 * (fuel p.1).length + p.2,
        !((toWord (fuel p.1).length (v p.1)).reverse.getD p.2 false))) := by
    fun_prop
  unfold forbid
  exact Groundwork.PolyT.map hbody hrange

@[fun_prop] theorem entries_polyT {α : Type} [Enc α]
    {blocks : α → Blocks} {domain : α → List Nat}
    (hb : PolyT blocks) (hd : PolyT domain) :
    PolyT (fun x => entries (blocks x) (domain x)) := by
  have hrange : PolyT (fun x => List.range (blocks x).length) :=
    Groundwork.PolyT.range (Groundwork.Unary.of_length hb)
  unfold entries
  fun_prop

@[fun_prop] theorem matrixAt_polyT {α : Type} [Enc α]
    {matrix : α → Matrix} {x y : α → Nat}
    (hm : PolyT matrix) (hx : PolyT x) (hy : PolyT y) :
    PolyT (fun a => matrixAt (matrix a) (x a) (y a)) := by
  unfold matrixAt
  fun_prop

@[fun_prop] theorem compatible_polyT {α : Type} [Enc α]
    {blocks : α → Blocks} {matrix : α → Matrix}
    {i j u v : α → Nat}
    (hb : PolyT blocks) (hm : PolyT matrix)
    (hi : PolyT i) (hj : PolyT j) (hu : PolyT u) (hv : PolyT v) :
    PolyT (fun x => compatible (blocks x) (matrix x) (i x) (j x) (u x) (v x)) := by
  unfold compatible
  fun_prop

@[fun_prop] theorem invalidEntries_polyT {α : Type} [Enc α]
    {blocks : α → Blocks} {domain : α → List Nat}
    (hb : PolyT blocks) (hd : PolyT domain) :
    PolyT (fun x => invalidEntries (blocks x) (domain x)) := by
  unfold invalidEntries
  fun_prop

@[fun_prop] theorem badPairEntries_polyT {α : Type} [Enc α]
    {blocks : α → Blocks} {matrix : α → Matrix} {domain : α → List Nat}
    (hb : PolyT blocks) (hm : PolyT matrix) (hd : PolyT domain) :
    PolyT (fun x => badPairEntries (blocks x) (matrix x) (domain x)) := by
  unfold badPairEntries
  fun_prop

theorem encode_polyT :
    PolyT (fun p : (Blocks × Matrix) × (List Nat × List Unit) =>
      encode p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold encode
  fun_prop

private theorem bool_imp_iff (m : Bool) (A B : Prop)
    [Decidable A] [Decidable B] :
    (!(m && decide A && !(decide B)) = true) ↔ (m = true → A → B) := by
  cases m <;> by_cases hA : A <;> by_cases hB : B <;> simp_all

theorem compatible_eq_true_iff (blocks : Blocks) (matrix : Matrix)
    (i j u v : Nat) :
    compatible blocks matrix i j u v = true ↔
      ∀ r < (blocks.getD i []).length, ∀ t < (blocks.getD j []).length,
        matrixAt matrix ((blocks.getD i []).getD r 0)
          ((blocks.getD j []).getD t 0) = true → t < v → r < u := by
  simp only [compatible, List.all_eq_true, List.mem_range]
  constructor
  · intro h r hr t ht hm htv
    exact (bool_imp_iff _ (t < v) (r < u)).mp (h r hr t ht) hm htv
  · intro h r hr t ht
    exact (bool_imp_iff _ (t < v) (r < u)).mpr (h r hr t ht)

@[simp] theorem forbid_length (fuel : List Unit) (i v : Nat) :
    (forbid fuel i v).length = fuel.length := by
  simp [forbid]

@[simp] theorem entries_length (blocks : Blocks) (domain : List Nat) :
    (entries blocks domain).length = blocks.length * domain.length := by
  change ((List.range blocks.length) ×ˢ domain).length = _
  rw [List.length_product, List.length_range]

@[simp] theorem encode_numVars (blocks : Blocks) (matrix : Matrix)
    (domain : List Nat) (fuel : List Unit) :
    (encode blocks matrix domain fuel).1 = blocks.length * fuel.length := rfl

theorem encode_width (blocks : Blocks) (matrix : Matrix)
    (domain : List Nat) (fuel : List Unit) :
    ∀ clause ∈ (encode blocks matrix domain fuel).2,
      clause.length ≤ 2 * fuel.length := by
  intro clause hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
    simp only [forbid_length]
    omega
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
    simp [forbid_length, Nat.two_mul]

theorem encode_clause_count (blocks : Blocks) (matrix : Matrix)
    (domain : List Nat) (fuel : List Unit) :
    (encode blocks matrix domain fuel).2.length ≤
      blocks.length * domain.length +
        (blocks.length * domain.length) * (blocks.length * domain.length) := by
  have hu : (invalidEntries blocks domain).length ≤ blocks.length * domain.length := by
    exact (List.length_filter_le _ _).trans (entries_length blocks domain).le
  have hb : (badPairEntries blocks matrix domain).length ≤
      (blocks.length * domain.length) * (blocks.length * domain.length) := by
    calc
      (badPairEntries blocks matrix domain).length ≤
          ((entries blocks domain).product (entries blocks domain)).length := by
            exact List.length_filter_le _ _
      _ = _ := by
        change ((entries blocks domain) ×ˢ (entries blocks domain)).length = _
        rw [List.length_product, entries_length]
  simpa only [encode, Prod.snd, List.length_append, List.length_map] using
    Nat.add_le_add hu hb

private theorem ofWord_append_single (w : List Bool) (bit : Bool) :
    ofWord (w ++ [bit]) = ofWord w + 2 ^ w.length * bit.toNat := by
  induction w with
  | nil => cases bit <;> rfl
  | cons b w ih =>
    simp only [List.cons_append, List.length_cons, ofWord, ih, pow_succ]
    ring

theorem bitEquiv_val (ℓ : Nat) (f : Fin ℓ → Bool) :
    (BinaryCSP.bitEquiv ℓ f).val = ofWord (List.ofFn f).reverse := by
  induction ℓ with
  | zero => simp [BinaryCSP.bitEquiv, ofWord]
  | succ n ih =>
    simp [BinaryCSP.bitEquiv, List.ofFn_succ, ofWord_append_single, ih]
    cases f 0 <;> simp [finTwoEquiv, Fin.tail_def]

/-- The finite-domain code stores the most significant bit first, whereas
`toWord` stores the least significant bit first. -/
theorem bitEquiv_word (ℓ : Nat) (v : Fin (2 ^ ℓ)) :
    List.ofFn ((BinaryCSP.bitEquiv ℓ).symm v) = (toWord ℓ v.val).reverse := by
  let f := (BinaryCSP.bitEquiv ℓ).symm v
  have hv : ofWord (List.ofFn f).reverse = v.val := by
    rw [← bitEquiv_val]
    simp [f]
  have hw := toWord_ofWord ((List.ofFn f).reverse)
  simp only [List.length_reverse, List.length_ofFn] at hw
  rw [hv] at hw
  simpa [f] using (congrArg List.reverse hw).symm

theorem range_eq_map_finRange (n : Nat) :
    List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem <;> simp

theorem forbid_eq_generic {b ℓ : Nat} (fuel : List Unit)
    (hlen : fuel.length = ℓ) (i : Fin b) (v : Fin (2 ^ ℓ)) :
    forbid fuel i.val v.val =
      (BinaryCSP.forbid i v).map (fun lit => (lit.1.val, lit.2)) := by
  unfold forbid BinaryCSP.forbid
  rw [hlen, range_eq_map_finRange]
  simp only [List.map_map]
  congr 1
  funext k
  apply Prod.ext
  · simp [BinaryCSP.gridEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  · have hk := congrArg (fun w : List Bool => w.getD k.val false) (bitEquiv_word ℓ v)
    have hleft : (List.ofFn ((BinaryCSP.bitEquiv ℓ).symm v)).getD k.val false =
        (BinaryCSP.bitEquiv ℓ).symm v k := by
      rw [List.getD_eq_getElem (List.ofFn ((BinaryCSP.bitEquiv ℓ).symm v)) false (by simp)]
      simp
    rw [hleft] at hk
    exact congrArg (fun bit : Bool => !bit) hk.symm

end StableMatching.RawChainCut
