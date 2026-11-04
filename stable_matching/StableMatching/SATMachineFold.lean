import StableMatching.AnthropicBridge
import Wrap.CodingExists
import Wrap.Sim
import CountKSat.Host
import ToTuring.Poly.Basic
import ToTuring.Lib.List2
import ToTuring.Lib.List1b

/-!
# Executable SAT query engine for the matching reduction

The imported `Solution` theorem gives one finite-alphabet counter. Anthropic's
configuration coding turns its runs into a stepped program whose initialization,
step, and output are polynomial-time. Subsequent lemmas fold this program over
the matching reduction's query words.
-/

namespace StableMatching.SATMachineFold

open Groundwork Turing

/-- The actual Anthropic counter, with a polynomial-time stepped simulation.
The state-size bound is explicit and uniform in the query width and formula. -/
theorem exists_prepared_stepped_counter :
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∃ (K : Wrap.Coding M),
        Nonempty (IsPolyT (Wrap.sim K id id)) ∧
        ∀ (k : ℕ) (φ : StableMatching.CNF),
          (∀ D ∈ φ.clauses, D.length ≤ k) →
          (Wrap.sim K id id).Runs
            (MainResults.encInput (max k 2) φ.prepare.clauses)
            (MainResults.timeMin C (max k 2) φ.prepare.clauses.length
              φ.prepare.numVars)
            (K.a * ((MainResults.encInput (max k 2) φ.prepare.clauses).length + 1) +
              K.a * MainResults.timeMin C (max k 2) φ.prepare.clauses.length
                φ.prepare.numVars)
            (MainResults.binary φ.prepare.numVars φ.satCount) := by
  obtain ⟨M, C, hfinite, hcount⟩ :=
    StableMatching.anthropic_prepared_machine_actual
  obtain ⟨K⟩ := Wrap.coding_exists M hfinite
  refine ⟨M, C, hfinite, K, ⟨Wrap.sim_isPolyT K PolyT.id' PolyT.id'⟩, ?_⟩
  intro k φ hwidth
  obtain ⟨hrun, heq⟩ := hcount k φ hwidth
  have houtput : Wrap.Outputs M
      (MainResults.encInput (max k 2) φ.prepare.clauses)
      (MainResults.binary φ.prepare.numVars
        (MainResults.numSat φ.prepare.clauses))
      (MainResults.timeMin C (max k 2) φ.prepare.clauses.length
        φ.prepare.numVars) := hrun
  simpa only [MainResults.encInput, id_eq, heq] using
    (Wrap.sim_runs K id id houtput)

/-! The query-list traversal does not inspect the query width. The same
program and the same host exponent therefore apply when the matching block
parameters vary with the input size. -/

/-- At each step retain the current query word and the unvisited tail. -/
def start (words : List (List Bool)) : Option (List Bool × List (List Bool)) :=
  words.head?.map fun word => (word, words.tail)

def next (cursor : List Bool × List (List Bool)) :
    Option (List Bool × List (List Bool)) :=
  start cursor.2

theorem start_polyT : PolyT start := by
  unfold start
  fun_prop

theorem next_polyT : PolyT next :=
  start_polyT.comp (by fun_prop)

/-- The exact finite orbit of `start` and `next`. -/
def cursors : List (List Bool) → List (List Bool × List (List Bool))
  | [] => []
  | word :: tail => (word, tail) :: cursors tail

theorem cursors_orbit (words : List (List Bool)) :
    Stepped.Orbit next (start words) (cursors words) := by
  induction words with
  | nil => exact Stepped.Orbit.nil
  | cons word tail ih =>
      simpa only [start, next, cursors, List.head?_cons, List.tail_cons,
        Option.map_some] using (Stepped.Orbit.cons ih)

/-- Decode each SAT output word and retain the same underlying computation. -/
def wordCounter {M : TM2ComputableAux Bool Bool} (K : Wrap.Coding M) :
    Stepped (List Bool) ℕ :=
  Stepped.mapOut (Wrap.sim K id id) ofWord

theorem satCount_le_pow (φ : StableMatching.CNF) :
    φ.satCount ≤ 2 ^ φ.numVars := by
  classical
  unfold StableMatching.CNF.satCount
  exact (Finset.card_filter_le _ _).trans (by simp)

private theorem toWord_eq (length value : ℕ) :
    toWord length value = (List.range length).map value.testBit := by
  induction length generalizing value with
  | zero => rfl
  | succ length ih =>
      rw [toWord, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · simp [Nat.testBit_zero]
      · refine List.map_congr_left fun i _ => ?_
        simp [Nat.testBit_succ]

theorem ofWord_binary (n value : ℕ) (hvalue : value ≤ 2 ^ n) :
    ofWord (MainResults.binary n value) = value := by
  have hpow : 0 < 2 ^ n := pow_pos (by norm_num) _
  have hlt : value < 2 ^ (n + 1) := by
    rw [pow_succ]
    omega
  rw [MainResults.binary, ← toWord_eq]
  exact ofWord_toWord hlt

/-- The stepped query engine reads the counter's output word as the exact
number of satisfying assignments. -/
theorem wordCounter_runs {M : TM2ComputableAux Bool Bool}
    (K : Wrap.Coding M) {n k time : ℕ} (clauses : MainResults.CNF n)
    (h : MainResults.CountsWithin M k clauses time) :
    (wordCounter K).Runs (MainResults.encInput k clauses) time
      (K.a * ((MainResults.encInput k clauses).length + 1) + K.a * time)
      (MainResults.numSat clauses) := by
  have houtput : Wrap.Outputs M (MainResults.encInput k clauses)
      (MainResults.binary n (MainResults.numSat clauses)) time := h
  have hrun := Stepped.mapOut_runs (f := ofWord)
    (Wrap.sim_runs K id id houtput)
  have hle : MainResults.numSat clauses ≤ 2 ^ n := by
    classical
    unfold MainResults.numSat
    exact (Finset.card_filter_le _ _).trans (by simp)
  simpa only [wordCounter, MainResults.encInput, id_eq,
    ofWord_binary n (MainResults.numSat clauses) hle] using hrun

@[instance_reducible] def wordCounter_isPolyT {M : TM2ComputableAux Bool Bool}
    (K : Wrap.Coding M) : IsPolyT (wordCounter K) := by
  letI : IsPolyT (Wrap.sim K id id) :=
    Wrap.sim_isPolyT K PolyT.id' PolyT.id'
  exact IsPolyT.mapOut (Groundwork.PolyT.ofWord' PolyT.id')

/-- One fixed program sums the outputs on any list of encoded SAT queries. -/
def sumProgram {M : TM2ComputableAux Bool Bool} (K : Wrap.Coding M) :
    Stepped (List (List Bool)) ℕ :=
  Stepped.foldWhile start next
    (Stepped.mapIn (fun p : List Bool × List (List Bool) => p.1) (wordCounter K))
    (fun count _ value => count + value) (fun _ => 0)

@[instance_reducible] def sumProgram_isPolyT {M : TM2ComputableAux Bool Bool}
    (K : Wrap.Coding M) : IsPolyT (sumProgram K) := by
  letI : IsPolyT (wordCounter K) := wordCounter_isPolyT K
  letI : IsPolyT (Stepped.mapIn
      (fun p : List Bool × List (List Bool) => p.1) (wordCounter K)) :=
    IsPolyT.mapIn (by fun_prop)
  exact IsPolyT.foldWhile start_polyT next_polyT (by fun_prop) (by fun_prop)

theorem cursors_firsts (words : List (List Bool)) :
    (cursors words).map Prod.fst = words := by
  induction words with
  | nil => rfl
  | cons word tail ih => simp [cursors, ih]

private theorem foldl_sum {α : Type} (f : α → ℕ)
    (xs : List α) (initial : ℕ) :
    xs.foldl (fun total x => total + f x) initial =
      initial + (xs.map f).sum := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      omega

/-- The fixed summing program runs one SAT query per input word and returns
their sum. The accumulator-size premise is kept explicit for the final market
count bound; it is a bound on binary size, not on the numeric count itself. -/
theorem sumProgram_runs {M : TM2ComputableAux Bool Bool}
    (K : Wrap.Coding M) (words : List (List Bool))
    (time value : List Bool → ℕ) (Sx Sc Sm : ℕ)
    (hbody : ∀ word ∈ words,
      (wordCounter K).Runs word (time word) Sm (value word))
    (hx : ∀ p ∈ cursors words, size p ≤ Sx)
    (hc : ∀ pre, pre <+: cursors words →
      size (pre.foldl (fun total p => total + value p.1) 0) ≤ Sc) :
    (sumProgram K).Runs words
      ((words.map fun word => time word + 1).sum)
      (Sx + (Sc + Sm) + 1)
      ((words.map value).sum) := by
  have hinner : ∀ p ∈ cursors words,
      (Stepped.mapIn (fun p : List Bool × List (List Bool) => p.1)
        (wordCounter K)).Runs p (time p.1) Sm (value p.1) := by
    intro p hp
    have hmem : p.1 ∈ words := by
      have hfirst : p.1 ∈ (cursors words).map Prod.fst :=
        List.mem_map_of_mem hp
      simpa only [cursors_firsts] using hfirst
    exact Stepped.mapIn_runs (hbody p.1 hmem)
  have hrun := Stepped.foldWhile_runs
    (start := start) (nxt := next)
    (M := Stepped.mapIn (fun p : List Bool × List (List Bool) => p.1)
      (wordCounter K))
    (g := fun total _ count => total + count)
    (c₀ := fun _ : List (List Bool) => 0)
    (a := words) (xs := cursors words)
    (cursors_orbit words)
    (fun p => time p.1) (fun p => value p.1)
    Sx Sc Sm hinner hx hc
  have htime :
      ((cursors words).map fun p => time p.1 + 1).sum =
      ((words.map fun word => time word + 1).sum) := by
    calc
      _ = (((cursors words).map Prod.fst).map
          fun word => time word + 1).sum := by simp [List.map_map, Function.comp_def]
      _ = _ := by rw [cursors_firsts]
  have hvalue :
      ((cursors words).map fun p => value p.1).sum =
      (words.map value).sum := by
    calc
      _ = (((cursors words).map Prod.fst).map value).sum := by
        simp [List.map_map, Function.comp_def]
      _ = _ := by rw [cursors_firsts]
  have hfold :
      (cursors words).foldl (fun total p => total + value p.1) 0 =
      (words.map value).sum := by
    simpa only [Nat.zero_add, hvalue] using
      (foldl_sum (fun p => value p.1) (cursors words) 0)
  simpa only [sumProgram, htime, hfold] using hrun

/-- The same run bound indexed by cursor position. This form permits repeated
query words and separate source formulas or time bounds at each occurrence. -/
theorem sumProgram_runs_cursor {M : TM2ComputableAux Bool Bool}
    (K : Wrap.Coding M) (words : List (List Bool))
    (time value : List Bool × List (List Bool) → ℕ) (Sx Sc Sm : ℕ)
    (hbody : ∀ p ∈ cursors words,
      (wordCounter K).Runs p.1 (time p) Sm (value p))
    (hx : ∀ p ∈ cursors words, size p ≤ Sx)
    (hc : ∀ pre, pre <+: cursors words →
      size (pre.foldl (fun total p => total + value p) 0) ≤ Sc) :
    (sumProgram K).Runs words
      (((cursors words).map fun p => time p + 1).sum)
      (Sx + (Sc + Sm) + 1)
      ((cursors words).map value).sum := by
  have hinner : ∀ p ∈ cursors words,
      (Stepped.mapIn (fun p : List Bool × List (List Bool) => p.1)
        (wordCounter K)).Runs p (time p) Sm (value p) := by
    intro p hp
    exact Stepped.mapIn_runs (hbody p hp)
  have hrun := Stepped.foldWhile_runs
    (start := start) (nxt := next)
    (M := Stepped.mapIn (fun p : List Bool × List (List Bool) => p.1)
      (wordCounter K))
    (g := fun total _ count => total + count)
    (c₀ := fun _ : List (List Bool) => 0)
    (a := words) (xs := cursors words)
    (cursors_orbit words) time value
    Sx Sc Sm hinner hx hc
  have hfold :
      (cursors words).foldl (fun total p => total + value p) 0 =
      ((cursors words).map value).sum := by
    simpa only [Nat.zero_add] using
      (foldl_sum value (cursors words) 0)
  simpa only [sumProgram, hfold] using hrun

/-- One fixed polynomial-time summing program together with the exact run of
its SAT body on every prepared CNF. The same witness serves all query widths. -/
theorem exists_prepared_sum_program :
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∃ (K : Wrap.Coding M),
        Nonempty (IsPolyT (sumProgram K)) ∧
        ∀ (k : ℕ) (φ : StableMatching.CNF),
          (∀ D ∈ φ.clauses, D.length ≤ k) →
          (wordCounter K).Runs
            (MainResults.encInput (max k 2) φ.prepare.clauses)
            (MainResults.timeMin C (max k 2) φ.prepare.clauses.length
              φ.prepare.numVars)
            (K.a * ((MainResults.encInput (max k 2) φ.prepare.clauses).length + 1) +
              K.a * MainResults.timeMin C (max k 2) φ.prepare.clauses.length
                φ.prepare.numVars)
            φ.satCount := by
  obtain ⟨M, C, hfinite, hcount⟩ :=
    StableMatching.anthropic_prepared_machine_actual
  obtain ⟨K⟩ := Wrap.coding_exists M hfinite
  refine ⟨M, C, hfinite, K, ⟨sumProgram_isPolyT K⟩, ?_⟩
  intro k φ hwidth
  obtain ⟨hrun, heq⟩ := hcount k φ hwidth
  have hr := wordCounter_runs K φ.prepare.clauses hrun
  simpa only [heq] using hr

end StableMatching.SATMachineFold

#print axioms StableMatching.anthropic_prepared_machine_actual
#print axioms StableMatching.SATMachineFold.exists_prepared_stepped_counter
#print axioms StableMatching.SATMachineFold.exists_prepared_sum_program
