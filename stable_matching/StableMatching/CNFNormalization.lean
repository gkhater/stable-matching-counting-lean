import StableMatching.Formula
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card

/-! Removing repeated clause lists preserves the exact number of satisfying
assignments.  This is the syntactic normalization required by
`MainResults.IsKCNF`; clauses with the same literals in another order remain
distinct, just as in the source theorem. -/

namespace StableMatching

def CNF.eraseDuplicateClauses (φ : CNF) : CNF :=
  { φ with clauses := φ.clauses.dedup }

@[simp] theorem CNF.eraseDuplicateClauses_numVars (φ : CNF) :
    φ.eraseDuplicateClauses.numVars = φ.numVars := rfl

@[simp] theorem CNF.eraseDuplicateClauses_clauses (φ : CNF) :
    φ.eraseDuplicateClauses.clauses = φ.clauses.dedup := rfl

theorem CNF.eraseDuplicateClauses_nodup (φ : CNF) :
    φ.eraseDuplicateClauses.clauses.Nodup := List.nodup_dedup _

theorem CNF.satisfies_eraseDuplicateClauses (φ : CNF)
    (a : Fin φ.numVars → Bool) :
    φ.eraseDuplicateClauses.Satisfies a ↔ φ.Satisfies a := by
  constructor
  · intro h C hC
    exact h C (List.mem_dedup.mpr hC)
  · intro h C hC
    exact h C (List.mem_dedup.mp hC)

theorem CNF.satCount_eraseDuplicateClauses (φ : CNF) :
    φ.eraseDuplicateClauses.satCount = φ.satCount := by
  cases φ with
  | mk n clauses =>
    classical
    unfold CNF.satCount
    apply congrArg Finset.card
    exact @Finset.filter_congr (Fin n → Bool)
      (fun a => (⟨n, clauses⟩ : CNF).eraseDuplicateClauses.Satisfies a)
      (fun a => (⟨n, clauses⟩ : CNF).Satisfies a)
      (Classical.decPred _) (Classical.decPred _) Finset.univ
      (by intro a _; exact CNF.satisfies_eraseDuplicateClauses ⟨n, clauses⟩ a)

/-- A tautological clause for every variable makes occurrence explicit without
changing the assignment set. The list is intentionally deduplicated separately. -/
def CNF.withOccurrenceTautologies (φ : CNF) : CNF :=
  { φ with clauses := φ.clauses ++
      (List.finRange φ.numVars).map (fun i => [(i, true), (i, false)]) }

theorem CNF.satisfies_withOccurrenceTautologies (φ : CNF)
    (a : Fin φ.numVars → Bool) :
    φ.withOccurrenceTautologies.Satisfies a ↔ φ.Satisfies a := by
  cases φ with
  | mk n clauses =>
    constructor
    · intro h C hC
      exact h C (List.mem_append.mpr (Or.inl hC))
    · intro h C hC
      rcases List.mem_append.mp hC with hC | hC
      · exact h C hC
      · rcases List.mem_map.mp hC with ⟨i, _, rfl⟩
        cases hb : a i with
        | false =>
          exact ⟨(i, false),
            List.mem_cons_of_mem (i, true) List.mem_cons_self, hb⟩
        | true => exact ⟨(i, true), List.mem_cons_self, hb⟩

theorem CNF.satCount_withOccurrenceTautologies (φ : CNF) :
    φ.withOccurrenceTautologies.satCount = φ.satCount := by
  cases φ with
  | mk n clauses =>
    classical
    unfold CNF.satCount
    apply congrArg Finset.card
    exact @Finset.filter_congr (Fin n → Bool)
      (fun a => (⟨n, clauses⟩ : CNF).withOccurrenceTautologies.Satisfies a)
      (fun a => (⟨n, clauses⟩ : CNF).Satisfies a)
      (Classical.decPred _) (Classical.decPred _) Finset.univ
      (by intro a _; exact CNF.satisfies_withOccurrenceTautologies ⟨n, clauses⟩ a)

theorem CNF.withOccurrenceTautologies_allOccur (φ : CNF) :
    ∀ i : Fin φ.numVars, ∃ C ∈ φ.withOccurrenceTautologies.clauses,
      ∃ l ∈ C, l.1 = i := by
  intro i
  refine ⟨[(i, true), (i, false)], ?_, (i, true), by simp, rfl⟩
  apply List.mem_append.mpr
  right
  apply List.mem_map.mpr
  exact ⟨i, List.mem_finRange i, rfl⟩

theorem CNF.withOccurrenceTautologies_width (φ : CNF) (k : ℕ)
    (hwidth : ∀ C ∈ φ.clauses, C.length ≤ k) :
    ∀ C ∈ φ.withOccurrenceTautologies.clauses,
      C.length ≤ max k 2 := by
  intro C hC
  rcases List.mem_append.mp hC with hC | hC
  · exact (hwidth C hC).trans (Nat.le_max_left k 2)
  · rcases List.mem_map.mp hC with ⟨i, _, rfl⟩
    change 2 ≤ max k 2
    exact Nat.le_max_right k 2

/-- Preserve every old literal while adding four fresh variables. -/
def CNF.castFourLiteral {n : ℕ} (l : Fin n × Bool) : Fin (n + 4) × Bool :=
  (Fin.castAdd 4 l.1, l.2)

/-- Four fresh variables are each fixed false by a separate unit clause. -/
def CNF.padFour (φ : CNF) : CNF where
  numVars := φ.numVars + 4
  clauses := φ.clauses.map (fun C => C.map castFourLiteral) ++
    (List.finRange 4).map (fun j => [(Fin.natAdd φ.numVars j, false)])

def CNF.restrictFour (φ : CNF) (b : Fin (φ.numVars + 4) → Bool) :
    Fin φ.numVars → Bool := fun i => b (Fin.castAdd 4 i)

def CNF.extendFour (φ : CNF) (a : Fin φ.numVars → Bool) :
    Fin (φ.numVars + 4) → Bool := Fin.addCases a (fun _ => false)

theorem CNF.padFour_satisfies_iff (φ : CNF)
    (b : Fin (φ.numVars + 4) → Bool) :
    φ.padFour.Satisfies b ↔ φ.Satisfies (φ.restrictFour b) ∧
      ∀ j : Fin 4, b (Fin.natAdd φ.numVars j) = false := by
  cases φ with
  | mk n clauses =>
    constructor
    · intro h
      constructor
      · intro C hC
        have hCp : C.map castFourLiteral ∈ (⟨n, clauses⟩ : CNF).padFour.clauses := by
          exact List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨C, hC, rfl⟩))
        rcases h _ hCp with ⟨l, hl, heq⟩
        rcases List.mem_map.mp hl with ⟨l₀, hl₀, rfl⟩
        exact ⟨l₀, hl₀, heq⟩
      · intro j
        have hU : [(Fin.natAdd n j, false)] ∈
            (⟨n, clauses⟩ : CNF).padFour.clauses := by
          exact List.mem_append.mpr (Or.inr
            (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))
        rcases h _ hU with ⟨l, hl, heq⟩
        have hl' : l = (Fin.natAdd n j, false) := List.mem_singleton.mp hl
        simpa only [hl'] using heq
    · rintro ⟨hOld, hFresh⟩ C hC
      rcases List.mem_append.mp hC with hC | hC
      · rcases List.mem_map.mp hC with ⟨C₀, hC₀, rfl⟩
        rcases hOld C₀ hC₀ with ⟨l₀, hl₀, heq⟩
        exact ⟨castFourLiteral l₀,
          List.mem_map.mpr ⟨l₀, hl₀, rfl⟩, heq⟩
      · rcases List.mem_map.mp hC with ⟨j, _, rfl⟩
        exact ⟨(Fin.natAdd n j, false), List.mem_cons_self, hFresh j⟩

theorem CNF.restrictFour_extendFour (φ : CNF)
    (a : Fin φ.numVars → Bool) :
    φ.restrictFour (φ.extendFour a) = a := by
  funext i
  simp [restrictFour, extendFour]

theorem CNF.extendFour_restrictFour (φ : CNF)
    (b : Fin (φ.numVars + 4) → Bool)
    (hFresh : ∀ j : Fin 4, b (Fin.natAdd φ.numVars j) = false) :
    φ.extendFour (φ.restrictFour b) = b := by
  have hright : (fun _ : Fin 4 => false) =
      (fun j => b (Fin.natAdd φ.numVars j)) := by
    funext j
    exact (hFresh j).symm
  funext i
  change Fin.addCases (fun j => b (Fin.castAdd 4 j))
    (fun _ : Fin 4 => false) i = b i
  rw [hright]
  exact Fin.addCases_castAdd_natAdd b i

theorem CNF.satCount_padFour (φ : CNF) :
    φ.padFour.satCount = φ.satCount := by
  cases φ with
  | mk n clauses =>
    classical
    unfold CNF.satCount
    refine Finset.card_bij'
      (fun b _ => (⟨n, clauses⟩ : CNF).restrictFour b)
      (fun a _ => (⟨n, clauses⟩ : CNF).extendFour a)
      ?_ ?_ ?_ ?_
    · intro b hb
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact ((CNF.padFour_satisfies_iff ⟨n, clauses⟩ b).mp
        (Finset.mem_filter.mp hb).2).1
    · intro a ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply (CNF.padFour_satisfies_iff ⟨n, clauses⟩ _).mpr
      constructor
      · simpa only [CNF.restrictFour_extendFour] using
          (Finset.mem_filter.mp ha).2
      · intro j
        simp [CNF.extendFour]
    · intro b hb
      exact CNF.extendFour_restrictFour ⟨n, clauses⟩ b
        ((CNF.padFour_satisfies_iff ⟨n, clauses⟩ b).mp
          (Finset.mem_filter.mp hb).2).2
    · intro a _
      exact CNF.restrictFour_extendFour ⟨n, clauses⟩ a

theorem CNF.padFour_width (φ : CNF) (k : ℕ)
    (hwidth : ∀ C ∈ φ.clauses, C.length ≤ k) :
    ∀ C ∈ φ.padFour.clauses, C.length ≤ max k 2 := by
  cases φ with
  | mk n clauses =>
    intro C hC
    rcases List.mem_append.mp hC with hC | hC
    · rcases List.mem_map.mp hC with ⟨C₀, hC₀, rfl⟩
      calc
        (C₀.map castFourLiteral).length = C₀.length := by simp
        _ ≤ max k 2 := (hwidth C₀ hC₀).trans (Nat.le_max_left k 2)
    · rcases List.mem_map.mp hC with ⟨j, _, rfl⟩
      change 1 ≤ max k 2
      exact (by omega)

theorem CNF.padFour_fresh_unit_mem (φ : CNF) (j : Fin 4) :
    [(Fin.natAdd φ.numVars j, false)] ∈ φ.padFour.clauses := by
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩

private theorem two_le_length_of_mem_ne {α : Type*} {l : List α}
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) :
    2 ≤ l.length := by
  cases l with
  | nil => cases hx
  | cons a t =>
    cases t with
    | nil =>
      have hx' : x = a := by simpa using hx
      have hy' : y = a := by simpa using hy
      exact False.elim (hne (hx'.trans hy'.symm))
    | cons b t => simp

theorem CNF.padFour_dedup_two_le (φ : CNF) :
    2 ≤ φ.padFour.eraseDuplicateClauses.clauses.length := by
  let u₀ : List (Fin (φ.numVars + 4) × Bool) :=
    [(Fin.natAdd φ.numVars (0 : Fin 4), false)]
  let u₁ : List (Fin (φ.numVars + 4) × Bool) :=
    [(Fin.natAdd φ.numVars (1 : Fin 4), false)]
  have h₀ : u₀ ∈ φ.padFour.eraseDuplicateClauses.clauses := by
    change u₀ ∈ φ.padFour.clauses.dedup
    exact List.mem_dedup.mpr (φ.padFour_fresh_unit_mem 0)
  have h₁ : u₁ ∈ φ.padFour.eraseDuplicateClauses.clauses := by
    change u₁ ∈ φ.padFour.clauses.dedup
    exact List.mem_dedup.mpr (φ.padFour_fresh_unit_mem 1)
  have hne : u₀ ≠ u₁ := by
    simp [u₀, u₁, Fin.natAdd]
  exact two_le_length_of_mem_ne h₀ h₁ hne

/-- Put an arbitrary CNF in the numerical domain of the counting theorem.
The four fresh unit clauses fix their variables, occurrence tautologies expose
every variable, and deduplication removes repeated clause lists. -/
def CNF.prepare (φ : CNF) : CNF :=
  φ.padFour.withOccurrenceTautologies.eraseDuplicateClauses

@[simp] theorem CNF.prepare_numVars (φ : CNF) :
    φ.prepare.numVars = φ.numVars + 4 := rfl

theorem CNF.satCount_prepare (φ : CNF) :
    φ.prepare.satCount = φ.satCount := by
  calc
    φ.prepare.satCount = φ.padFour.withOccurrenceTautologies.satCount :=
      φ.padFour.withOccurrenceTautologies.satCount_eraseDuplicateClauses
    _ = φ.padFour.satCount := φ.padFour.satCount_withOccurrenceTautologies
    _ = φ.satCount := φ.satCount_padFour

theorem CNF.prepare_nodup (φ : CNF) : φ.prepare.clauses.Nodup :=
  φ.padFour.withOccurrenceTautologies.eraseDuplicateClauses_nodup

theorem CNF.prepare_width (φ : CNF) (k : ℕ)
    (hwidth : ∀ C ∈ φ.clauses, C.length ≤ k) :
    ∀ C ∈ φ.prepare.clauses, C.length ≤ max k 2 := by
  intro C hC
  have h := φ.padFour.withOccurrenceTautologies_width (max k 2)
    (φ.padFour_width k hwidth) C (List.mem_dedup.mp hC)
  rw [max_eq_left (Nat.le_max_right k 2)] at h
  exact h

theorem CNF.prepare_allOccur (φ : CNF) :
    ∀ i : Fin φ.prepare.numVars, ∃ C ∈ φ.prepare.clauses,
      ∃ l ∈ C, l.1 = i := by
  intro i
  obtain ⟨C, hC, l, hl, hi⟩ := φ.padFour.withOccurrenceTautologies_allOccur i
  exact ⟨C, List.mem_dedup.mpr hC, l, hl, hi⟩

theorem CNF.prepare_two_le (φ : CNF) : 2 ≤ φ.prepare.clauses.length := by
  let u₀ : List (Fin (φ.numVars + 4) × Bool) :=
    [(Fin.natAdd φ.numVars (0 : Fin 4), false)]
  let u₁ : List (Fin (φ.numVars + 4) × Bool) :=
    [(Fin.natAdd φ.numVars (1 : Fin 4), false)]
  have h₀ : u₀ ∈ φ.prepare.clauses := by
    change u₀ ∈ φ.padFour.withOccurrenceTautologies.clauses.dedup
    apply List.mem_dedup.mpr
    exact List.mem_append.mpr (Or.inl (φ.padFour_fresh_unit_mem 0))
  have h₁ : u₁ ∈ φ.prepare.clauses := by
    change u₁ ∈ φ.padFour.withOccurrenceTautologies.clauses.dedup
    apply List.mem_dedup.mpr
    exact List.mem_append.mpr (Or.inl (φ.padFour_fresh_unit_mem 1))
  have hne : u₀ ≠ u₁ := by
    simp [u₀, u₁, Fin.natAdd]
  exact two_le_length_of_mem_ne h₀ h₁ hne

end StableMatching
