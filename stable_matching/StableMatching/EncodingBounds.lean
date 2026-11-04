import ToTuring.EncLemmas

/-! Lower bounds on the actual encoded length for the standard size instances. -/

namespace StableMatching.EncodingBounds

open Groundwork

theorem size_bools (bits : List Bool) : size bits = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    rw [size_list, List.map_cons, List.sum_cons, size_bool]
    rw [size_list] at ih
    simp only [List.length_cons]
    omega

theorem length_le_size {A : Type} [HasSize A] (xs : List A) : xs.length ≤ size xs := by
  induction xs with
  | nil => simp [size_list]
  | cons a xs ih =>
    rw [size_list, List.map_cons, List.sum_cons]
    rw [size_list] at ih
    simp only [List.length_cons]
    omega

theorem size_nat_le_len (n : Nat) : size n ≤ len n := by
  rw [size_nat, len_nat]
  omega

theorem size_bool_le_len (b : Bool) : size b ≤ len b := by
  rw [size_bool, len_bool]

theorem size_list_le_len {A : Type} [HasSize A] [Enc A]
    (h : ∀ a : A, size a ≤ len a) (xs : List A) : size xs ≤ len xs := by
  induction xs with
  | nil => simp [size_list, len_nil]
  | cons a xs ih =>
    have ha := h a
    rw [len_cons, size_list, List.map_cons, List.sum_cons]
    rw [size_list] at ih
    omega

theorem size_pair_le_len {A B : Type} [HasSize A] [HasSize B] [Enc A] [Enc B]
    (ha : ∀ a : A, size a ≤ len a) (hb : ∀ b : B, size b ≤ len b) (p : A × B) :
    size p ≤ len p := by
  have h1 := ha p.1
  have h2 := hb p.2
  rw [size_prod, len_pair]
  omega

theorem size_matrix_le_len (matrix : List (List Bool)) : size matrix ≤ len matrix :=
  size_list_le_len (size_list_le_len size_bool_le_len) matrix

theorem size_rank_input_le_len (raw : List (List Nat) × List (List Nat)) : size raw ≤ len raw :=
  size_pair_le_len (size_list_le_len (size_list_le_len size_nat_le_len))
    (size_list_le_len (size_list_le_len size_nat_le_len)) raw

theorem size_traversal_input_le_len
    (raw : List (List Bool) × Nat × List Nat) : size raw ≤ len raw :=
  size_pair_le_len size_matrix_le_len
    (size_pair_le_len size_nat_le_len (size_list_le_len size_nat_le_len)) raw

end StableMatching.EncodingBounds
