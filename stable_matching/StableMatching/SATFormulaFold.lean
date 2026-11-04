import StableMatching.SATCursorIndex
import StableMatching.MatchingAccumulatorBounds
import StepMachines.Prog.SideBasics

/-! The fixed SAT summing program on the actual stable-matching query list. -/

namespace StableMatching.SATFormulaFold

open Groundwork MathEconLib.Matching
open SATMachineFold

def encodeQuery (n : Nat) (φ : CNF) : List Bool :=
  MainResults.encInput (UniformCounting.width n) φ.prepare.clauses

def words {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n)) :
    List (List Bool) :=
  (UniformCounting.queries mkt).map (encodeQuery n)

def selected {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (cursor : SATCursorIndex.Cursor) : CNF :=
  (UniformCounting.queries mkt).getD
    (SATCursorIndex.index (UniformCounting.queries mkt).length cursor) ⟨0, []⟩

noncomputable def cursorTime {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (C : Nat) (cursor : SATCursorIndex.Cursor) : Nat :=
  MainResults.timeMin C (UniformCounting.width n)
    (selected mkt cursor).prepare.clauses.length
    (selected mkt cursor).prepare.numVars

noncomputable def cursorValue {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (cursor : SATCursorIndex.Cursor) : Nat :=
  (selected mkt cursor).satCount

private theorem cursor_size_le (ws : List (List Bool))
    (cursor : SATCursorIndex.Cursor) (h : cursor ∈ cursors ws) :
    Groundwork.size cursor ≤ Groundwork.size ws := by
  induction ws with
  | nil => simp [cursors] at h
  | cons w ws ih =>
      rcases List.mem_cons.mp h with rfl | ht
      · simp only [Groundwork.size_prod, Groundwork.size_list,
          List.map_cons, List.sum_cons]
        omega
      · have hle := ih ht
        simp only [Groundwork.size_list, List.map_cons, List.sum_cons] at hle ⊢
        omega

private theorem foldl_sum {α : Type} (f : α → Nat) (xs : List α)
    (initial : Nat) :
    xs.foldl (fun total x => total + f x) initial =
      initial + (xs.map f).sum := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      omega

theorem selected_mem {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (cursor : SATCursorIndex.Cursor) (h : cursor ∈ cursors (words mkt)) :
    selected mkt cursor ∈ UniformCounting.queries mkt := by
  have hi := SATCursorIndex.index_lt (words mkt) cursor h
  simp only [words, List.length_map] at hi
  unfold selected
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem selected_word {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (cursor : SATCursorIndex.Cursor) (h : cursor ∈ cursors (words mkt)) :
    encodeQuery n (selected mkt cursor) = cursor.1 := by
  unfold words at h
  exact SATCursorIndex.encoded_current (encodeQuery n) ⟨0, []⟩
    (UniformCounting.queries mkt) cursor h

theorem cursor_times {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n))
    (C : Nat) :
    ((cursors (words mkt)).map (cursorTime mkt C)) =
      (UniformCounting.queries mkt).map (fun φ =>
        MainResults.timeMin C (UniformCounting.width n)
          φ.prepare.clauses.length φ.prepare.numVars) := by
  exact SATCursorIndex.map_statistic (encodeQuery n)
    (fun φ => MainResults.timeMin C (UniformCounting.width n)
      φ.prepare.clauses.length φ.prepare.numVars) ⟨0, []⟩
    (UniformCounting.queries mkt)

theorem cursor_values {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n)) :
    ((cursors (words mkt)).map (cursorValue mkt)) =
      (UniformCounting.queries mkt).map CNF.satCount := by
  exact SATCursorIndex.map_statistic (encodeQuery n) CNF.satCount ⟨0, []⟩
    (UniformCounting.queries mkt)

theorem values_sum {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n)) :
    ((UniformCounting.queries mkt).map CNF.satCount).sum =
      Nat.card mkt.StableMatching := by
  rw [← UniformCounting.count_correct mkt]
  congr 1
  apply List.map_congr_left
  intro φ _
  rw [← CNF.satCount_eq_anthropic_numSat, CNF.satCount_prepare]

theorem cursor_prefix_size_le {n : Nat}
    (mkt : MarriageMarket (Fin n) (Fin n))
    (pre : List SATCursorIndex.Cursor)
    (hpre : pre <+: cursors (words mkt)) :
    Groundwork.size
      (pre.foldl (fun total cursor => total + cursorValue mkt cursor) 0) ≤
        n * n + 2 := by
  have hp : (pre.map (cursorValue mkt)).Sublist
      ((UniformCounting.queries mkt).map CNF.satCount) := by
    have hh := hpre.map (cursorValue mkt)
    rw [cursor_values] at hh
    exact hh.sublist
  rw [foldl_sum]
  simp only [Nat.zero_add]
  exact MatchingAccumulatorBounds.sublist_size_le mkt _ _ (values_sum mkt) hp

theorem prepared_sum_runs {M : Turing.TM2ComputableAux Bool Bool}
    (K : Wrap.Coding M) (C : Nat)
    (hcounter : ∀ (k : Nat) (φ : CNF),
      (∀ D ∈ φ.clauses, D.length ≤ k) →
      (wordCounter K).Runs
        (MainResults.encInput (max k 2) φ.prepare.clauses)
        (MainResults.timeMin C (max k 2) φ.prepare.clauses.length
          φ.prepare.numVars)
        (K.a * ((MainResults.encInput (max k 2) φ.prepare.clauses).length + 1) +
          K.a * MainResults.timeMin C (max k 2) φ.prepare.clauses.length
            φ.prepare.numVars) φ.satCount)
    {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n)) :
    (sumProgram K).Runs (words mkt)
      (((UniformCounting.queries mkt).map (fun φ =>
        MainResults.timeMin C (UniformCounting.width n)
          φ.prepare.clauses.length φ.prepare.numVars + 1)).sum)
      (Groundwork.size (words mkt) +
        ((n * n + 2) +
          (K.a * (Groundwork.size (words mkt) + 1) +
            K.a * ((UniformCounting.queries mkt).map (fun φ =>
              MainResults.timeMin C (UniformCounting.width n)
                φ.prepare.clauses.length φ.prepare.numVars)).sum)) + 1)
      (Nat.card mkt.StableMatching) := by
  let qs := UniformCounting.queries mkt
  let ws := words mkt
  let ts := (qs.map fun φ => MainResults.timeMin C (UniformCounting.width n)
    φ.prepare.clauses.length φ.prepare.numVars).sum
  have hbody : ∀ cursor ∈ cursors ws,
      (wordCounter K).Runs cursor.1 (cursorTime mkt C cursor)
        (K.a * (Groundwork.size ws + 1) + K.a * ts)
        (cursorValue mkt cursor) := by
    intro cursor hc
    let φ := selected mkt cursor
    have hφ : φ ∈ qs := selected_mem mkt cursor hc
    have hwidth : ∀ D ∈ φ.clauses,
        D.length ≤ 2 * ExecutableSchedule.bitWidth n := by
      exact CompactReduction.reduce_width mkt
        (ExecutableSchedule.blockLength n)
        (ExecutableSchedule.blockLength_pos n)
        (ExecutableSchedule.bitWidth n) φ hφ
    have hr := hcounter (2 * ExecutableSchedule.bitWidth n) φ hwidth
    have hword : MainResults.encInput (UniformCounting.width n)
        φ.prepare.clauses = cursor.1 := selected_word mkt cursor hc
    have hcursor : Groundwork.size cursor ≤ Groundwork.size ws :=
      cursor_size_le ws cursor hc
    have hwordlen : cursor.1.length ≤ Groundwork.size ws := by
      have hsize : cursor.1.length ≤ Groundwork.size cursor.1 := by
        rw [Groundwork.Prog.size_bools]
        omega
      rw [Groundwork.size_prod] at hcursor
      omega
    have htmem : cursorTime mkt C cursor ∈
        (cursors ws).map (cursorTime mkt C) := List.mem_map_of_mem hc
    have htle : cursorTime mkt C cursor ≤ ts := by
      rw [cursor_times] at htmem
      exact List.le_sum_of_mem htmem
    change (wordCounter K).Runs (encodeQuery n φ) (cursorTime mkt C cursor)
      (K.a * ((encodeQuery n φ).length + 1) + K.a * cursorTime mkt C cursor)
      (cursorValue mkt cursor) at hr
    change encodeQuery n φ = cursor.1 at hword
    rw [hword] at hr
    apply hr.mono (Nat.le_refl _)
    · dsimp only [ts]
      simp only [UniformCounting.width] at hr ⊢
      exact Nat.add_le_add (Nat.mul_le_mul_left K.a (by omega))
        (Nat.mul_le_mul_left K.a htle)
  have hx : ∀ cursor ∈ cursors ws,
      Groundwork.size cursor ≤ Groundwork.size ws := by
    intro cursor hc
    exact cursor_size_le ws cursor hc
  have hrun := sumProgram_runs_cursor K ws (cursorTime mkt C)
    (cursorValue mkt) (Groundwork.size ws) (n * n + 2)
    (K.a * (Groundwork.size ws + 1) + K.a * ts)
    hbody hx (cursor_prefix_size_le mkt)
  rw [cursor_values, values_sum] at hrun
  have htime : ((cursors ws).map fun cursor => cursorTime mkt C cursor + 1).sum =
      (qs.map fun φ => MainResults.timeMin C (UniformCounting.width n)
        φ.prepare.clauses.length φ.prepare.numVars + 1).sum := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (fun xs : List Nat => (xs.map (· + 1)).sum) (cursor_times mkt C)
  simpa only [htime, ts, ws, qs] using hrun

/-- One actual fixed polynomial-time SAT fold computes the exact market count. -/
theorem exists_prepared_sum_runs :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : Nat),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∃ (K : Wrap.Coding M), Nonempty (IsPolyT (sumProgram K)) ∧
        ∀ {n : Nat} (mkt : MarriageMarket (Fin n) (Fin n)),
          (sumProgram K).Runs (words mkt)
            (((UniformCounting.queries mkt).map (fun φ =>
              MainResults.timeMin C (UniformCounting.width n)
                φ.prepare.clauses.length φ.prepare.numVars + 1)).sum)
            (Groundwork.size (words mkt) +
              ((n * n + 2) +
                (K.a * (Groundwork.size (words mkt) + 1) +
                  K.a * ((UniformCounting.queries mkt).map (fun φ =>
                    MainResults.timeMin C (UniformCounting.width n)
                      φ.prepare.clauses.length φ.prepare.numVars)).sum)) + 1)
            (Nat.card mkt.StableMatching) := by
  obtain ⟨M, C, hfinite, K, hpoly, hcounter⟩ :=
    SATMachineFold.exists_prepared_sum_program
  exact ⟨M, C, hfinite, K, hpoly, fun mkt =>
    prepared_sum_runs K C hcounter mkt⟩

end StableMatching.SATFormulaFold
