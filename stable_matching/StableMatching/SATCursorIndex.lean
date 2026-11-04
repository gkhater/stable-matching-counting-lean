import StableMatching.SATMachineFold

/-! Positions connect the fixed word-list machine to formulas, even when
different positions carry identical encoded query words. -/

namespace StableMatching.SATCursorIndex

open SATMachineFold

abbrev Cursor := List Bool × List (List Bool)

def index (length : Nat) (cursor : Cursor) : Nat := length - (cursor.2.length + 1)

theorem tail_length_lt (words : List (List Bool)) (cursor : Cursor)
    (h : cursor ∈ cursors words) : cursor.2.length < words.length := by
  induction words with
  | nil => simp [cursors] at h
  | cons word tail ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · simp
    · have := ih ht
      simp only [List.length_cons]
      omega

theorem index_lt (words : List (List Bool)) (cursor : Cursor)
    (h : cursor ∈ cursors words) : index words.length cursor < words.length := by
  have := tail_length_lt words cursor h
  unfold index
  omega

theorem current_word (words : List (List Bool)) (cursor : Cursor)
    (h : cursor ∈ cursors words) : words.getD (index words.length cursor) [] = cursor.1 := by
  induction words with
  | nil => simp [cursors] at h
  | cons word tail ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · simp [index]
    · have hlt := tail_length_lt tail cursor ht
      have he : index (word :: tail).length cursor = index tail.length cursor + 1 := by
        simp only [index, List.length_cons]
        omega
      rw [he, List.getD_cons_succ]
      exact ih ht

theorem map_statistic {A B : Type} (encode : A → List Bool) (stat : A → B)
    (default : A) (xs : List A) :
    (cursors (xs.map encode)).map (fun cursor => stat (xs.getD (index xs.length cursor) default)) =
      xs.map stat := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, cursors, List.map_cons]
    have hhead : index (a :: xs).length (encode a, xs.map encode) = 0 := by simp [index]
    rw [hhead]
    simp only [List.getD_cons_zero]
    congr 1
    trans (cursors (xs.map encode)).map (fun cursor => stat (xs.getD (index xs.length cursor) default))
    · apply List.map_congr_left
      intro cursor hc
      have hlt := tail_length_lt (xs.map encode) cursor hc
      have he : index (a :: xs).length cursor = index xs.length cursor + 1 := by
        simp only [List.length_map] at hlt
        simp only [index, List.length_cons]
        omega
      rw [he, List.getD_cons_succ]
    · exact ih

theorem encoded_current {A : Type} (encode : A → List Bool) (default : A)
    (xs : List A) (cursor : Cursor) (h : cursor ∈ cursors (xs.map encode)) :
    encode (xs.getD (index xs.length cursor) default) = cursor.1 := by
  have hidx := index_lt (xs.map encode) cursor h
  simp only [List.length_map] at hidx
  have hw := current_word (xs.map encode) cursor h
  simp only [List.length_map] at hw
  rw [List.getD_eq_getElem _ [] (by simpa using hidx), List.getElem_map] at hw
  rw [List.getD_eq_getElem _ default hidx]
  exact hw

end StableMatching.SATCursorIndex
