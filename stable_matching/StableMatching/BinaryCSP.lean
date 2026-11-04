import StableMatching.PosetEncoding
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Binary CNF for finite unary and binary constraints

Every one of `b` domain variables has `2^ℓ` values, represented by `ℓ`
Boolean variables. A forbidden value contributes an `ℓ`-literal clause;
a forbidden pair contributes a clause of length `2*ℓ`.
-/

namespace StableMatching.BinaryCSP

variable {b ℓ : ℕ}

/-- Unary and binary predicates on the power-of-two domain. -/
structure Spec (b ℓ : ℕ) where
  valid : Fin b → Fin (2 ^ ℓ) → Prop
  compatible : Fin b → Fin b → Fin (2 ^ ℓ) → Fin (2 ^ ℓ) → Prop
  validDecide : ∀ i v, Decidable (valid i v)
  compatibleDecide : ∀ i j u v, Decidable (compatible i j u v)

def Spec.Solution (s : Spec b ℓ) (c : Fin b → Fin (2 ^ ℓ)) : Prop :=
  (∀ i, s.valid i (c i)) ∧
    (∀ i j, s.compatible i j (c i) (c j))

/-- Positions in a Boolean assignment are pairs of a domain variable and a bit. -/
def gridEquiv (b ℓ : ℕ) :
    (Fin b × Fin ℓ) ≃ Fin (b * ℓ) := finProdFinEquiv

/-- Each Boolean word has exactly one value in the power-of-two domain. -/
def bitEquiv : (ℓ : ℕ) → (Fin ℓ → Bool) ≃ Fin (2 ^ ℓ)
  | 0 =>
    { toFun := fun _ => 0
      invFun := fun _ i => Fin.elim0 i
      left_inv := by intro f; funext i; exact Fin.elim0 i
      right_inv := by intro x; apply Fin.ext; omega }
  | n + 1 =>
    ((Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).symm).trans
      (finTwoEquiv.symm.prodCongr (bitEquiv n)) |>.trans
        finProdFinEquiv |>.trans (finCongr (by simp [pow_succ, mul_comm]))

/-- Decode an assignment, one `ℓ`-bit block at a time. -/
def codes (a : Fin (b * ℓ) → Bool) : Fin b → Fin (2 ^ ℓ) :=
  fun i => bitEquiv ℓ (fun k => a (gridEquiv b ℓ (i, k)))

/-- Encoding and decoding give a bijection, including the zero-bit case. -/
def assignmentEquivCodes (b ℓ : ℕ) :
    (Fin (b * ℓ) → Bool) ≃ (Fin b → Fin (2 ^ ℓ)) where
  toFun := codes
  invFun c v :=
    let p := (gridEquiv b ℓ).symm v
    (bitEquiv ℓ).symm (c p.1) p.2
  left_inv a := by
    funext v
    simp [codes]
  right_inv c := by
    funext i
    simp [codes]

/-- One clause excludes one complete bit pattern at block `i`. -/
def forbid (i : Fin b) (v : Fin (2 ^ ℓ)) :
    List (Fin (b * ℓ) × Bool) :=
  (List.finRange ℓ).map fun k =>
    (gridEquiv b ℓ (i, k), !((bitEquiv ℓ).symm v k))

@[simp] theorem forbid_length (i : Fin b) (v : Fin (2 ^ ℓ)) :
    (forbid i v).length = ℓ := by simp [forbid]

private theorem bool_eq_not_iff_ne (x y : Bool) : x = !y ↔ x ≠ y := by
  cases x <;> cases y <;> decide

/-- The clause excludes precisely its named domain value. -/
theorem forbid_sat_iff (a : Fin (b * ℓ) → Bool) (i : Fin b)
    (v : Fin (2 ^ ℓ)) :
    (∃ literal ∈ forbid i v, a literal.1 = literal.2) ↔ codes a i ≠ v := by
  classical
  have hbits :
      (∃ k : Fin ℓ,
        a (gridEquiv b ℓ (i, k)) = !((bitEquiv ℓ).symm v k)) ↔
      (fun k => a (gridEquiv b ℓ (i, k))) ≠ (bitEquiv ℓ).symm v := by
    constructor
    · rintro ⟨k, hk⟩ heq
      exact (bool_eq_not_iff_ne _ _).mp hk (congrFun heq k)
    · intro hneq
      by_contra hn
      apply hneq
      funext k
      by_cases heq : a (gridEquiv b ℓ (i, k)) = (bitEquiv ℓ).symm v k
      · exact heq
      · exact False.elim (hn ⟨k, (bool_eq_not_iff_ne _ _).mpr heq⟩)
  rw [show (∃ literal ∈ forbid i v, a literal.1 = literal.2) ↔
      ∃ k : Fin ℓ, a (gridEquiv b ℓ (i, k)) = !((bitEquiv ℓ).symm v k) by
    simp [forbid]]
  rw [hbits]
  change (fun k => a (gridEquiv b ℓ (i, k))) ≠ (bitEquiv ℓ).symm v ↔
    bitEquiv ℓ (fun k => a (gridEquiv b ℓ (i, k))) ≠ v
  constructor
  · intro h hval
    exact h (by simpa using congrArg (bitEquiv ℓ).symm hval)
  · intro h hbitsEq
    exact h (by simpa [hbitsEq])

def allEntries (b ℓ : ℕ) : List (Fin b × Fin (2 ^ ℓ)) :=
  (List.finRange b).product (List.finRange (2 ^ ℓ))

theorem allEntries_length (b ℓ : ℕ) :
    (allEntries b ℓ).length = b * 2 ^ ℓ := by
  change ((List.finRange b) ×ˢ (List.finRange (2 ^ ℓ))).length = _
  rw [List.length_product, List.length_finRange, List.length_finRange]

def Spec.validTest (s : Spec b ℓ) (i : Fin b) (v : Fin (2 ^ ℓ)) : Bool :=
  @decide (s.valid i v) (s.validDecide i v)

def Spec.compatibleTest (s : Spec b ℓ) (i j : Fin b)
    (u v : Fin (2 ^ ℓ)) : Bool :=
  @decide (s.compatible i j u v) (s.compatibleDecide i j u v)

def invalidEntries (s : Spec b ℓ) : List (Fin b × Fin (2 ^ ℓ)) :=
  (allEntries b ℓ).filter fun p => s.validTest p.1 p.2 = false

@[simp] theorem mem_invalidEntries (s : Spec b ℓ) (p : Fin b × Fin (2 ^ ℓ)) :
    p ∈ invalidEntries s ↔ ¬s.valid p.1 p.2 := by
  classical
  rcases p with ⟨i, v⟩
  simp [invalidEntries, allEntries, Spec.validTest]

def badPairEntries (s : Spec b ℓ) :
    List ((Fin b × Fin (2 ^ ℓ)) × (Fin b × Fin (2 ^ ℓ))) :=
  ((allEntries b ℓ).product (allEntries b ℓ)).filter fun p =>
    s.compatibleTest p.1.1 p.2.1 p.1.2 p.2.2 = false

@[simp] theorem mem_badPairEntries (s : Spec b ℓ)
    (p : (Fin b × Fin (2 ^ ℓ)) × (Fin b × Fin (2 ^ ℓ))) :
    p ∈ badPairEntries s ↔ ¬s.compatible p.1.1 p.2.1 p.1.2 p.2.2 := by
  classical
  rcases p with ⟨⟨i, u⟩, ⟨j, v⟩⟩
  simp [badPairEntries, allEntries, Spec.compatibleTest]

def cnf (s : Spec b ℓ) : CNF where
  numVars := b * ℓ
  clauses :=
    (invalidEntries s).map (fun p => forbid p.1 p.2) ++
      (badPairEntries s).map (fun p => forbid p.1.1 p.1.2 ++ forbid p.2.1 p.2.2)

@[simp] theorem cnf_numVars (s : Spec b ℓ) : (cnf s).numVars = b * ℓ := rfl

/-- A Boolean assignment satisfies the CNF exactly when its decoded codes
satisfy all unary and binary predicates. -/
theorem satisfies_iff (s : Spec b ℓ) (a : Fin (b * ℓ) → Bool) :
    (cnf s).Satisfies a ↔ s.Solution (codes a) := by
  classical
  change (∀ clause ∈
      (invalidEntries s).map (fun p => forbid p.1 p.2) ++
        (badPairEntries s).map
          (fun p => forbid p.1.1 p.1.2 ++ forbid p.2.1 p.2.2),
      ∃ literal ∈ clause, a literal.1 = literal.2) ↔ _
  constructor
  · intro h
    constructor
    · intro i
      by_contra hn
      have hm : forbid i (codes a i) ∈
          (invalidEntries s).map (fun p => forbid p.1 p.2) ++
            (badPairEntries s).map
              (fun p => forbid p.1.1 p.1.2 ++ forbid p.2.1 p.2.2) := by
        apply List.mem_append.mpr
        left
        apply List.mem_map.mpr
        exact ⟨(i, codes a i), (mem_invalidEntries s _).mpr hn, rfl⟩
      exact (forbid_sat_iff a i (codes a i)).mp (h _ hm) rfl
    · intro i j
      by_contra hn
      have hm : forbid i (codes a i) ++ forbid j (codes a j) ∈
          (invalidEntries s).map (fun p => forbid p.1 p.2) ++
            (badPairEntries s).map
              (fun p => forbid p.1.1 p.1.2 ++ forbid p.2.1 p.2.2) := by
        apply List.mem_append.mpr
        right
        apply List.mem_map.mpr
        exact ⟨((i, codes a i), (j, codes a j)),
          (mem_badPairEntries s _).mpr hn, rfl⟩
      obtain ⟨literal, hl, ha⟩ := h _ hm
      rcases List.mem_append.mp hl with hl | hl
      · exact (forbid_sat_iff a i (codes a i)).mp ⟨literal, hl, ha⟩ rfl
      · exact (forbid_sat_iff a j (codes a j)).mp ⟨literal, hl, ha⟩ rfl
  · rintro ⟨hu, hb⟩ clause hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      apply (forbid_sat_iff a p.1 p.2).mpr
      intro heq
      exact (mem_invalidEntries s p).mp hp (heq ▸ hu p.1)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      by_cases heq : codes a p.1.1 = p.1.2
      · have hneq : codes a p.2.1 ≠ p.2.2 := by
          intro heq'
          have hcompat := hb p.1.1 p.2.1
          rw [heq, heq'] at hcompat
          exact (mem_badPairEntries s p).mp hp hcompat
        obtain ⟨literal, hl, ha⟩ := (forbid_sat_iff a p.2.1 p.2.2).mpr hneq
        exact ⟨literal, List.mem_append.mpr (Or.inr hl), ha⟩
      · obtain ⟨literal, hl, ha⟩ := (forbid_sat_iff a p.1.1 p.1.2).mpr heq
        exact ⟨literal, List.mem_append.mpr (Or.inl hl), ha⟩

/-- Satisfying Boolean assignments and domain solutions are in bijection. -/
noncomputable def satisfyingEquivSolutions (s : Spec b ℓ) :
    {a : Fin (b * ℓ) → Bool // (cnf s).Satisfies a} ≃
      {c : Fin b → Fin (2 ^ ℓ) // s.Solution c} where
  toFun a := ⟨assignmentEquivCodes b ℓ a.1,
    (satisfies_iff s a.1).mp a.2⟩
  invFun c := ⟨(assignmentEquivCodes b ℓ).symm c.1,
    (satisfies_iff s _).mpr (by
      change s.Solution ((assignmentEquivCodes b ℓ)
        ((assignmentEquivCodes b ℓ).symm c.1))
      rw [Equiv.apply_symm_apply]
      exact c.2)⟩
  left_inv a := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp

/-- Exact count preservation without auxiliary variables. -/
theorem satCount_eq_card_solutions (s : Spec b ℓ) :
    (cnf s).satCount = Nat.card {c : Fin b → Fin (2 ^ ℓ) // s.Solution c} := by
  classical
  calc
    (cnf s).satCount =
        Fintype.card {a : Fin (cnf s).numVars → Bool // (cnf s).Satisfies a} := by
      exact (Fintype.card_subtype _).symm
    _ = Nat.card {a : Fin (b * ℓ) → Bool // (cnf s).Satisfies a} :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card {c : Fin b → Fin (2 ^ ℓ) // s.Solution c} :=
      Nat.card_congr (satisfyingEquivSolutions s)

/-- Every unary clause has width `ℓ`; every binary clause has width `2*ℓ`. -/
theorem clause_width (s : Spec b ℓ) :
    ∀ clause ∈ (cnf s).clauses, clause.length ≤ 2 * ℓ := by
  change ∀ clause ∈ (invalidEntries s).map (fun p => forbid p.1 p.2) ++
    (badPairEntries s).map
      (fun p => forbid p.1.1 p.1.2 ++ forbid p.2.1 p.2.2),
    clause.length ≤ 2 * ℓ
  intro clause hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
    simp only [forbid_length]
    omega
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
    simp [forbid_length, Nat.two_mul]

/-- The clause list is at most quadratic in the number of domain assignments. -/
theorem clause_count (s : Spec b ℓ) :
    (cnf s).clauses.length ≤
      b * 2 ^ ℓ + (b * 2 ^ ℓ) * (b * 2 ^ ℓ) := by
  classical
  have hu : (invalidEntries s).length ≤ b * 2 ^ ℓ := by
    calc
      (invalidEntries s).length ≤ (allEntries b ℓ).length := by
        unfold invalidEntries
        exact List.length_filter_le _ _
      _ = b * 2 ^ ℓ := allEntries_length b ℓ
  have hb : (badPairEntries s).length ≤
      (b * 2 ^ ℓ) * (b * 2 ^ ℓ) := by
    calc
      (badPairEntries s).length ≤
          ((allEntries b ℓ).product (allEntries b ℓ)).length := by
        unfold badPairEntries
        exact List.length_filter_le _ _
      _ = (b * 2 ^ ℓ) * (b * 2 ^ ℓ) := by
        change ((allEntries b ℓ) ×ˢ (allEntries b ℓ)).length = _
        rw [List.length_product, allEntries_length]
  change ((invalidEntries s).map (fun p => forbid p.1 p.2) ++
    (badPairEntries s).map
      (fun p => forbid p.1.1 p.1.2 ++ forbid p.2.1 p.2.2)).length ≤ _
  simpa only [List.length_append, List.length_map] using Nat.add_le_add hu hb

end StableMatching.BinaryCSP
