import StableMatching.BinaryCSP
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Compact binary encoding of chain cuts

An explicit labelled partition into ordered chain blocks identifies a lower
set by one cut in each block. The cut values are encoded by `ℓ` Boolean bits.
-/

namespace StableMatching.ChainCutEncoding


variable {P : Type*} [PartialOrder P] {b D ℓ : ℕ}

/-- An explicit partition into `b` nonempty ordered chains of length at most
`D`. The equivalence labels every poset element by its block and position. -/
structure ChainPartition (P : Type*) [PartialOrder P] (b D : ℕ) where
  len : Fin b → ℕ
  label : P ≃ (Σ i : Fin b, Fin (len i))
  chain_le : ∀ (i : Fin b) (j k : Fin (len i)), j ≤ k →
    label.symm ⟨i, j⟩ ≤ label.symm ⟨i, k⟩
  len_pos : ∀ i, 0 < len i
  len_le : ∀ i, len i ≤ D

variable (part : ChainPartition P b D)

namespace ChainPartition

/-- The cut is one past the greatest included position, or zero if empty. -/
noncomputable def rawCut (s : LowerSet P) (i : Fin b) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin (part.len i))).filter
    fun j => part.label.symm ⟨i, j⟩ ∈ s).sup fun j => j.val + 1

theorem rawCut_le_len (s : LowerSet P) (i : Fin b) :
    part.rawCut s i ≤ part.len i := by
  classical
  unfold rawCut
  apply Finset.sup_le
  intro j _
  omega

/-- A chain fiber of a lower set is exactly its prefix below the cut. -/
theorem mem_iff_lt_rawCut (s : LowerSet P) (i : Fin b)
    (j : Fin (part.len i)) :
    part.label.symm ⟨i, j⟩ ∈ s ↔ j.val < part.rawCut s i := by
  classical
  constructor
  · intro hj
    have hmem : j ∈ (Finset.univ : Finset (Fin (part.len i))).filter
        (fun k => part.label.symm ⟨i, k⟩ ∈ s) := by simp [hj]
    have hle : j.val + 1 ≤ part.rawCut s i := by
      unfold rawCut
      exact Finset.le_sup (f := fun k : Fin (part.len i) => (k.val + 1 : ℕ)) hmem
    omega
  · intro hj
    unfold rawCut at hj
    simp only [Finset.lt_sup_iff (α := ℕ)] at hj
    obtain ⟨k, hk, hlt⟩ := hj
    have hkS : part.label.symm ⟨i, k⟩ ∈ s := (Finset.mem_filter.mp hk).2
    have hjk : j ≤ k := by omega
    exact s.lower (part.chain_le i j k hjk) hkS

variable [DecidableLE P]

/-- A single domain variable ranges over all bit words. -/
def spec : BinaryCSP.Spec b ℓ where
  valid i v := v.val ≤ part.len i
  compatible i j u v :=
    ∀ (r : Fin (part.len i)) (t : Fin (part.len j)),
      part.label.symm ⟨i, r⟩ ≤ part.label.symm ⟨j, t⟩ →
      t.val < v.val → r.val < u.val
  validDecide := fun _ _ => inferInstance
  compatibleDecide := fun _ _ _ _ => inferInstance

/-- Enough bit capacity to represent every cut including the full-chain cut. -/
def Capacity (part : ChainPartition P b D) (ℓ : ℕ) : Prop := D + 1 ≤ 2 ^ ℓ

noncomputable def cut (hcap : part.Capacity ℓ) (s : LowerSet P)
    (i : Fin b) : Fin (2 ^ ℓ) :=
  ⟨part.rawCut s i, by
    have hlen := part.rawCut_le_len s i
    have hD := part.len_le i
    dsimp [Capacity] at hcap
    omega⟩

@[simp] theorem cut_val (hcap : part.Capacity ℓ) (s : LowerSet P)
    (i : Fin b) : (part.cut hcap s i).val = part.rawCut s i := rfl

theorem cut_solution (hcap : part.Capacity ℓ) (s : LowerSet P) :
    (part.spec (ℓ := ℓ)).Solution (part.cut hcap s) := by
  constructor
  · intro i
    exact part.rawCut_le_len s i
  · intro i j r t hle ht
    have htS : part.label.symm ⟨j, t⟩ ∈ s :=
      (part.mem_iff_lt_rawCut s j t).mpr ht
    exact (part.mem_iff_lt_rawCut s i r).mp (s.lower hle htS)

/-- A compatible vector of cuts defines a lower set. -/
def lowerSetOfSolution
    (c : {c : Fin b → Fin (2 ^ ℓ) // (part.spec (ℓ := ℓ)).Solution c}) :
    LowerSet P where
  carrier := {x | (part.label x).2.val < (c.1 (part.label x).1).val}
  lower' := by
    intro x y hyx hx
    have hrel : part.label.symm (part.label y) ≤
        part.label.symm (part.label x) := by simpa using hyx
    exact c.2.2 (part.label y).1 (part.label x).1
      (part.label y).2 (part.label x).2 hrel hx

theorem rawCut_lowerSetOfSolution
    (c : {c : Fin b → Fin (2 ^ ℓ) // (part.spec (ℓ := ℓ)).Solution c})
    (i : Fin b) :
    part.rawCut (part.lowerSetOfSolution c) i = (c.1 i).val := by
  classical
  have hupper : part.rawCut (part.lowerSetOfSolution c) i ≤ (c.1 i).val := by
    unfold rawCut
    apply Finset.sup_le
    intro j hj
    have hmem : j.val < (c.1 i).val := by
      have hh := (Finset.mem_filter.mp hj).2
      change (part.label (part.label.symm ⟨i, j⟩)).2.val <
        (c.1 (part.label (part.label.symm ⟨i, j⟩)).1).val at hh
      have hlabel : part.label (part.label.symm ⟨i, j⟩) = ⟨i, j⟩ :=
        part.label.apply_symm_apply _
      rw [hlabel] at hh
      exact hh
    omega
  have hlower : (c.1 i).val ≤ part.rawCut (part.lowerSetOfSolution c) i := by
    by_cases hz : (c.1 i).val = 0
    · omega
    · let j : Fin (part.len i) := ⟨(c.1 i).val - 1, by
        have hv := c.2.1 i
        dsimp [spec] at hv
        omega⟩
      have hj : j ∈ (Finset.univ : Finset (Fin (part.len i))).filter
          (fun k => part.label.symm ⟨i, k⟩ ∈ part.lowerSetOfSolution c) := by
        have hpos : (c.1 i).val - 1 < (c.1 i).val := by omega
        apply Finset.mem_filter.mpr
        constructor
        · simp
        · change (part.label (part.label.symm ⟨i, j⟩)).2.val <
            (c.1 (part.label (part.label.symm ⟨i, j⟩)).1).val
          have hlabel : part.label (part.label.symm ⟨i, j⟩) = ⟨i, j⟩ :=
            part.label.apply_symm_apply _
          rw [hlabel]
          exact hpos
      have hle : j.val + 1 ≤ part.rawCut (part.lowerSetOfSolution c) i := by
        unfold rawCut
        exact Finset.le_sup (f := fun k : Fin (part.len i) => (k.val + 1 : ℕ)) hj
      dsimp [j] at hle
      omega
  omega

/-- Chain cuts and lower sets are in bijection. -/
noncomputable def solutionEquivLowerSet (hcap : part.Capacity ℓ) :
    {c : Fin b → Fin (2 ^ ℓ) // (part.spec (ℓ := ℓ)).Solution c} ≃ LowerSet P where
  toFun := part.lowerSetOfSolution
  invFun s := ⟨part.cut hcap s, part.cut_solution hcap s⟩
  left_inv c := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact part.rawCut_lowerSetOfSolution c i
  right_inv s := by
    apply LowerSet.ext
    ext x
    have h := part.mem_iff_lt_rawCut s (part.label x).1 (part.label x).2
    simpa [lowerSetOfSolution] using h.symm

/-- The compact CNF uses exactly one `ℓ`-bit block per chain. -/
def cnf (ℓ : ℕ) : CNF := BinaryCSP.cnf (part.spec (ℓ := ℓ))

/-- Satisfying bit assignments are precisely lower sets. -/
noncomputable def satisfyingEquivLowerSet (hcap : part.Capacity ℓ) :
    {a : Fin (b * ℓ) → Bool // (part.cnf ℓ).Satisfies a} ≃ LowerSet P :=
  (BinaryCSP.satisfyingEquivSolutions (part.spec (ℓ := ℓ))).trans
    (part.solutionEquivLowerSet hcap)

theorem satCount_eq_card_lowerSet (hcap : part.Capacity ℓ) :
    (part.cnf ℓ).satCount = Nat.card (LowerSet P) := by
  calc
    (part.cnf ℓ).satCount =
        Nat.card {c : Fin b → Fin (2 ^ ℓ) // (part.spec (ℓ := ℓ)).Solution c} :=
      BinaryCSP.satCount_eq_card_solutions _
    _ = Nat.card (LowerSet P) := Nat.card_congr (part.solutionEquivLowerSet hcap)

@[simp] theorem cnf_numVars : (part.cnf ℓ).numVars = b * ℓ :=
  BinaryCSP.cnf_numVars _

theorem cnf_width :
    ∀ clause ∈ (part.cnf ℓ).clauses, clause.length ≤ 2 * ℓ :=
  BinaryCSP.clause_width _

/-- A nonempty chain block has a representative element, so the number of
blocks is at most the poset size. -/
theorem blocks_le_card (part : ChainPartition P b D) : b ≤ Nat.card P := by
  classical
  let : Fintype P := Fintype.ofEquiv _ part.label.symm
  let representative : Fin b → P := fun i =>
    part.label.symm ⟨i, ⟨0, part.len_pos i⟩⟩
  have hinj : Function.Injective representative := by
    intro i j h
    have h' := congrArg (fun x : P => (part.label x).1) h
    simpa [representative] using h'
  simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using
    (Fintype.card_le_of_injective representative hinj)

/-- Coarse polynomial clause bound in the poset size and bit-domain size. -/
theorem cnf_clause_count :
    (part.cnf ℓ).clauses.length ≤
      Nat.card P * 2 ^ ℓ + (Nat.card P * 2 ^ ℓ) * (Nat.card P * 2 ^ ℓ) := by
  have hraw := BinaryCSP.clause_count (part.spec (ℓ := ℓ))
  have hb := part.blocks_le_card
  have hm : b * 2 ^ ℓ ≤ Nat.card P * 2 ^ ℓ := Nat.mul_le_mul_right _ hb
  have hsq : (b * 2 ^ ℓ) * (b * 2 ^ ℓ) ≤
      (Nat.card P * 2 ^ ℓ) * (Nat.card P * 2 ^ ℓ) :=
    Nat.mul_le_mul hm hm
  exact hraw.trans (Nat.add_le_add hm hsq)

end ChainPartition
end StableMatching.ChainCutEncoding
