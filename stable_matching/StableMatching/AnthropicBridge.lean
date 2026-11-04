import StableMatching.CNFNormalization
import Solution

/-! A statement-level bridge to the exact proposition proved in the Anthropic
development. `MainResults.MainTheorem` is the machine theorem, with its original
input encoding, output encoding, and step count. The `Solution` import supplies
its Lean-checked proof through `MainResults.mainTheorem`. -/

namespace StableMatching

theorem CNF.satCount_eq_anthropic_numSat (φ : CNF) :
    φ.satCount = MainResults.numSat φ.clauses := by
  cases φ with
  | mk n clauses =>
    classical
    unfold CNF.satCount MainResults.numSat
    apply congrArg Finset.card
    ext a
    change (a ∈ (Finset.univ.filter fun a : Fin n → Bool =>
      (⟨n, clauses⟩ : CNF).Satisfies a)) ↔
      a ∈ (Finset.univ.filter fun a : Fin n → Bool =>
        ∀ C ∈ clauses, ∃ l ∈ C, a l.1 = l.2)
    constructor
    · intro ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a,
        (Finset.mem_filter.mp ha).2⟩
    · intro ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a,
        (Finset.mem_filter.mp ha).2⟩

theorem CNF.anthropic_numSat_eraseDuplicateClauses (φ : CNF) :
    MainResults.numSat φ.eraseDuplicateClauses.clauses = φ.satCount := by
  rw [← φ.eraseDuplicateClauses.satCount_eq_anthropic_numSat,
    φ.satCount_eraseDuplicateClauses]

theorem CNF.anthropic_allOccur_eraseDuplicateClauses (φ : CNF) :
    MainResults.AllOccur φ.eraseDuplicateClauses.clauses ↔
      MainResults.AllOccur φ.clauses := by
  cases φ with
  | mk n clauses =>
    constructor
    · intro h i
      rcases h i with ⟨C, hC, l, hl, hi⟩
      exact ⟨C, List.mem_dedup.mp hC, l, hl, hi⟩
    · intro h i
      rcases h i with ⟨C, hC, l, hl, hi⟩
      exact ⟨C, List.mem_dedup.mpr hC, l, hl, hi⟩

theorem CNF.anthropic_isKCNF_eraseDuplicateClauses (φ : CNF) (k : ℕ)
    (hwidth : ∀ C ∈ φ.clauses, C.length ≤ k) :
    MainResults.IsKCNF k φ.eraseDuplicateClauses.clauses := by
  refine ⟨?_, φ.eraseDuplicateClauses_nodup⟩
  intro C hC
  exact hwidth C (List.mem_dedup.mp hC)

/-- Exactly the domain on which the Anthropic machine theorem applies after
deduplicating identical clause lists. The clause count is the normalized count. -/
def CNF.AnthropicAdmissible (k : ℕ) (φ : CNF) : Prop :=
  1 ≤ k ∧
  (∀ C ∈ φ.clauses, C.length ≤ k) ∧
  2 ≤ φ.eraseDuplicateClauses.clauses.length ∧
  4 ≤ φ.numVars ∧
  MainResults.AllOccur φ.clauses

theorem CNF.anthropicAdmissible_of_nodup (φ : CNF) (k : ℕ)
    (hk : 1 ≤ k) (hwidth : ∀ C ∈ φ.clauses, C.length ≤ k)
    (hnodup : φ.clauses.Nodup) (hm : 2 ≤ φ.clauses.length)
    (hn : 4 ≤ φ.numVars) (hoccur : MainResults.AllOccur φ.clauses) :
    φ.AnthropicAdmissible k := by
  refine ⟨hk, hwidth, ?_, hn, hoccur⟩
  change 2 ≤ φ.clauses.dedup.length
  simpa only [hnodup.dedup] using hm

theorem CNF.prepare_anthropicAdmissible (φ : CNF) (k : ℕ)
    (hwidth : ∀ C ∈ φ.clauses, C.length ≤ k) :
    φ.prepare.AnthropicAdmissible (max k 2) := by
  refine ⟨by omega, φ.prepare_width k hwidth, ?_, by simp, ?_⟩
  · change 2 ≤ φ.prepare.clauses.dedup.length
    simpa only [φ.prepare_nodup.dedup] using φ.prepare_two_le
  · exact φ.prepare_allOccur

/-- Apply the original uniform machine proposition to every input CNF after
padding, occurrence completion, and duplicate removal. -/
theorem anthropic_prepared_machine (hMain : MainResults.MainTheorem) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (k : ℕ) (φ : CNF),
        (∀ D ∈ φ.clauses, D.length ≤ k) →
        MainResults.CountsWithin M (max k 2) φ.prepare.clauses
          (MainResults.timeMin C (max k 2) φ.prepare.clauses.length
            φ.prepare.numVars) ∧
        MainResults.numSat φ.prepare.clauses = φ.satCount := by
  rcases hMain with ⟨M, C, hfinite, hbound⟩
  refine ⟨M, C, hfinite, ?_⟩
  intro k φ hwidth
  have hp := φ.prepare_anthropicAdmissible k hwidth
  rcases hp with ⟨hk, hw, hm, hn, ho⟩
  refine ⟨hbound (max k 2) φ.prepare.numVars φ.prepare.clauses hk
    ⟨hw, φ.prepare_nodup⟩ ?_ hn ho, ?_⟩
  · change 2 ≤ φ.prepare.clauses.dedup.length at hm
    simpa only [φ.prepare_nodup.dedup] using hm
  · rw [← φ.prepare.satCount_eq_anthropic_numSat, φ.satCount_prepare]

/-- Apply the *original* machine proposition to the normalized formula. The
machine and constant are chosen once before any `k` or instance. The last
conjunct identifies its output count with `StableMatching.CNF.satCount`. -/
theorem anthropic_normalized_machine (hMain : MainResults.MainTheorem) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (k : ℕ) (φ : CNF), φ.AnthropicAdmissible k →
        MainResults.CountsWithin M k φ.eraseDuplicateClauses.clauses
          (MainResults.timeMin C k φ.eraseDuplicateClauses.clauses.length φ.numVars) ∧
        MainResults.numSat φ.eraseDuplicateClauses.clauses = φ.satCount := by
  rcases hMain with ⟨M, C, hfinite, hbound⟩
  refine ⟨M, C, hfinite, ?_⟩
  intro k φ hφ
  rcases hφ with ⟨hk, hwidth, hm, hn, hoccur⟩
  refine ⟨hbound k φ.numVars φ.eraseDuplicateClauses.clauses hk
    (φ.anthropic_isKCNF_eraseDuplicateClauses k hwidth) hm hn
    (φ.anthropic_allOccur_eraseDuplicateClauses.mpr hoccur),
    φ.anthropic_numSat_eraseDuplicateClauses⟩

/-- The prepared counting machine obtained from Anthropic's actual `Solution`
proof, for every width-bounded CNF including small and non-normalized inputs. -/
theorem anthropic_prepared_machine_actual :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (k : ℕ) (φ : CNF),
        (∀ D ∈ φ.clauses, D.length ≤ k) →
        MainResults.CountsWithin M (max k 2) φ.prepare.clauses
          (MainResults.timeMin C (max k 2) φ.prepare.clauses.length
            φ.prepare.numVars) ∧
        MainResults.numSat φ.prepare.clauses = φ.satCount :=
  anthropic_prepared_machine MainResults.mainTheorem

/-- The same imported machine theorem on the duplicate-free normalized input. -/
theorem anthropic_normalized_machine_actual :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (k : ℕ) (φ : CNF), φ.AnthropicAdmissible k →
        MainResults.CountsWithin M k φ.eraseDuplicateClauses.clauses
          (MainResults.timeMin C k φ.eraseDuplicateClauses.clauses.length φ.numVars) ∧
        MainResults.numSat φ.eraseDuplicateClauses.clauses = φ.satCount :=
  anthropic_normalized_machine MainResults.mainTheorem

end StableMatching
