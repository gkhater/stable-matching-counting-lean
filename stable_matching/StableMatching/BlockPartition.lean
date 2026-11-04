import StableMatching.ChainCutEncoding
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise

/-!
# Constructing a chain partition from explicit list blocks

The data constructor searches only the listed block positions. Its inverse
reads the element at a block and position, so the resulting CNF can be built
from computed ordered blocks.
-/

namespace StableMatching.BlockPartition

variable {P : Type*} [PartialOrder P] [DecidableEq P] {D : ℕ}

structure Data (P : Type*) [PartialOrder P] [DecidableEq P] (D : ℕ) where
  remaining : List P
  blocks : List (List P)
  remaining_nodup : remaining.Nodup
  flatten_perm : blocks.flatten.Perm remaining
  block_nonempty : ∀ l ∈ blocks, l ≠ []
  block_length_le : ∀ l ∈ blocks, l.length ≤ D
  block_pairwise : ∀ l ∈ blocks, l.Pairwise (· ≤ ·)

variable (d : Data P D)

namespace Data

abbrev Position := Σ i : Fin d.blocks.length, Fin (d.blocks.get i).length

def value (p : d.Position) : P := (d.blocks.get p.1).get p.2

theorem flatten_nodup : d.blocks.flatten.Nodup :=
  d.flatten_perm.nodup_iff.mpr d.remaining_nodup

theorem value_mem_flatten (p : d.Position) : d.value p ∈ d.blocks.flatten :=
  List.mem_flatten_of_mem (List.get_mem d.blocks p.1)
    (List.get_mem (d.blocks.get p.1) p.2)

def decode (p : d.Position) : {x : P // x ∈ d.remaining} :=
  ⟨d.value p, d.flatten_perm.mem_iff.mp (d.value_mem_flatten p)⟩

theorem value_injective : Function.Injective d.value := by
  intro p q h
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, t⟩
  have hparts := List.nodup_flatten.mp d.flatten_nodup
  by_cases hik : i = k
  · subst k
    have hnd : (d.blocks.get i).Nodup :=
      hparts.1 _ (List.get_mem d.blocks i)
    have hjt : j = t := hnd.get_inj_iff.mp h
    subst t
    rfl
  · rcases lt_or_gt_of_ne hik with hik | hki
    · have hd := hparts.2.rel_get_of_lt hik
      have hj : d.value ⟨i, j⟩ ∈ d.blocks.get i :=
        List.get_mem (d.blocks.get i) j
      have ht : d.value ⟨k, t⟩ ∈ d.blocks.get k :=
        List.get_mem (d.blocks.get k) t
      exact False.elim ((List.disjoint_left.mp hd) hj (h ▸ ht))
    · have hd := hparts.2.rel_get_of_lt hki
      have hj : d.value ⟨i, j⟩ ∈ d.blocks.get i :=
        List.get_mem (d.blocks.get i) j
      have ht : d.value ⟨k, t⟩ ∈ d.blocks.get k :=
        List.get_mem (d.blocks.get k) t
      exact False.elim ((List.disjoint_left.mp hd) ht (h.symm ▸ hj))

theorem decode_injective : Function.Injective d.decode := by
  intro p q h
  exact d.value_injective (congrArg Subtype.val h)

theorem exists_decode (x : {x : P // x ∈ d.remaining}) :
    ∃ p : d.Position, d.decode p = x := by
  have hx : x.1 ∈ d.blocks.flatten := d.flatten_perm.mem_iff.mpr x.2
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hl
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hxl
  refine ⟨⟨i, j⟩, ?_⟩
  apply Subtype.ext
  exact hj

/-- Every block position is listed once. -/
def positionList : List d.Position :=
  (List.finRange d.blocks.length).sigma
    (fun i => List.finRange (d.blocks.get i).length)

theorem positionList_nodup : d.positionList.Nodup := by
  unfold positionList
  exact (List.nodup_finRange _).sigma (fun i => List.nodup_finRange _)

theorem mem_positionList (p : d.Position) : p ∈ d.positionList := by
  rcases p with ⟨i, j⟩
  simp [positionList]

def decodedList : List {x : P // x ∈ d.remaining} :=
  d.positionList.map d.decode

theorem decodedList_nodup : d.decodedList.Nodup :=
  d.positionList_nodup.map d.decode_injective

theorem mem_decodedList (x : {x : P // x ∈ d.remaining}) :
    x ∈ d.decodedList := by
  obtain ⟨p, rfl⟩ := d.exists_decode x
  exact List.mem_map.mpr ⟨p, d.mem_positionList p, rfl⟩

/-- The first equivalence indexes the position list. -/
def positionEquiv : Fin d.positionList.length ≃ d.Position :=
  d.positionList_nodup.getEquivOfForallMemList d.positionList d.mem_positionList

/-- The second equivalence reads the element at the same list position. -/
def decodedEquiv : Fin d.positionList.length ≃ {x : P // x ∈ d.remaining} :=
  (finCongr (by simp [decodedList])).trans
    (d.decodedList_nodup.getEquivOfForallMemList d.decodedList d.mem_decodedList)

theorem decodedEquiv_apply (i : Fin d.positionList.length) :
    d.decodedEquiv i = d.decode (d.positionList.get i) := by
  simp [decodedEquiv, decodedList, List.Nodup.getEquivOfForallMemList]
  rfl

/-- The computable block-and-position labelling of the remaining elements. -/
def labelEquiv : {x : P // x ∈ d.remaining} ≃ d.Position :=
  d.decodedEquiv.symm.trans d.positionEquiv

theorem labelEquiv_symm_apply (p : d.Position) :
    d.labelEquiv.symm p = d.decode p := by
  change d.decodedEquiv (d.positionEquiv.symm p) = d.decode p
  rw [d.decodedEquiv_apply]
  have h := d.positionEquiv.apply_symm_apply p
  change d.positionList.get (d.positionEquiv.symm p) = p at h
  rw [h]

/-- Turn the explicit ordered blocks into the chain-partition input for the
compact cut encoder. The equivalence computes by searching the position list. -/
def chainPartition :
    ChainCutEncoding.ChainPartition
      {x : P // x ∈ d.remaining} d.blocks.length D where
  len := fun i => (d.blocks.get i).length
  label := d.labelEquiv
  chain_le := by
    intro i j k hjk
    rw [d.labelEquiv_symm_apply ⟨i, j⟩,
      d.labelEquiv_symm_apply ⟨i, k⟩]
    change (d.blocks.get i).get j ≤ (d.blocks.get i).get k
    by_cases heq : j = k
    · subst k
      exact le_rfl
    · exact (d.block_pairwise _ (List.get_mem d.blocks i)).rel_get_of_lt
        (lt_of_le_of_ne hjk heq)
  len_pos := by
    intro i
    have hne := d.block_nonempty _ (List.get_mem d.blocks i)
    cases hb : d.blocks.get i with
    | nil => exact False.elim (hne hb)
    | cons a l => simp
  len_le := by
    intro i
    exact d.block_length_le _ (List.get_mem d.blocks i)

variable [DecidableLE P]

/-- Executable compact CNF for the lower sets of the remaining poset. -/
def encode (ℓ : ℕ) : CNF := d.chainPartition.cnf ℓ

theorem encode_correct {ℓ : ℕ} (hcap : D + 1 ≤ 2 ^ ℓ) :
    (d.encode ℓ).satCount =
      Nat.card (LowerSet {x : P // x ∈ d.remaining}) :=
  d.chainPartition.satCount_eq_card_lowerSet hcap

@[simp] theorem encode_numVars (ℓ : ℕ) :
    (d.encode ℓ).numVars = d.blocks.length * ℓ :=
  d.chainPartition.cnf_numVars

theorem encode_width (ℓ : ℕ) :
    ∀ clause ∈ (d.encode ℓ).clauses, clause.length ≤ 2 * ℓ :=
  d.chainPartition.cnf_width

theorem encode_clause_count (ℓ : ℕ) :
    (d.encode ℓ).clauses.length ≤
      Nat.card {x : P // x ∈ d.remaining} * 2 ^ ℓ +
        (Nat.card {x : P // x ∈ d.remaining} * 2 ^ ℓ) *
          (Nat.card {x : P // x ∈ d.remaining} * 2 ^ ℓ) :=
  d.chainPartition.cnf_clause_count

theorem card_remaining : Nat.card {x : P // x ∈ d.remaining} = d.remaining.length := by
  have h := Nat.card_congr (d.remaining_nodup.getEquiv d.remaining)
  simpa using h.symm

theorem encode_clause_count_length (ℓ : ℕ) :
    (d.encode ℓ).clauses.length ≤
      d.remaining.length * 2 ^ ℓ +
        (d.remaining.length * 2 ^ ℓ) * (d.remaining.length * 2 ^ ℓ) := by
  simpa only [d.card_remaining] using d.encode_clause_count ℓ

end Data
end StableMatching.BlockPartition
