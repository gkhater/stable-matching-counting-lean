import StableMatching.RankDA

/-! Agreement of the costed rank-list implementation with MathEconLib's
existing simultaneous deferred-acceptance algorithm. -/

namespace StableMatching.RankDA

open MathEconLib.Matching
open MathEconLib.Matching.MarriageMarket

def boundedFinList {n : Nat} (xs : List Nat) (h : ∀ i ∈ xs, i < n) : List (Fin n) :=
  xs.attach.map (fun i => ⟨i.1, h i.1 i.2⟩)

theorem boundedFinList_map_val {n : Nat} (xs : List Nat) (h : ∀ i ∈ xs, i < n) :
    (boundedFinList xs h).map Fin.val = xs := by
  simp [boundedFinList, List.map_map, Function.comp_def]

theorem mem_boundedFinList {n : Nat} (xs : List Nat) (h : ∀ i ∈ xs, i < n) (j : Fin n) :
    j ∈ boundedFinList xs h ↔ j.val ∈ xs := by
  constructor
  · intro hj
    have hm : j.val ∈ (boundedFinList xs h).map Fin.val := List.mem_map.mpr ⟨j, hj, rfl⟩
    simpa only [boundedFinList_map_val] using hm
  · intro hj
    apply List.mem_map.mpr
    exact ⟨⟨j.val, hj⟩, List.mem_attach _ _, Fin.ext rfl⟩

theorem mem_pairs (rows : Rows) (p : Nat × Nat) :
    p ∈ pairs rows ↔ p.1 < rows.length ∧ p.2 < rows.length := by
  rcases p with ⟨m, w⟩
  change (m, w) ∈ (List.range rows.length) ×ˢ (List.range rows.length) ↔ _
  simp

theorem available_bounded (rows : Rows) (R : Contracts) (m : Nat) :
    ∀ w ∈ available rows R m, w < rows.length := by
  intro w hw
  exact List.mem_range.mp (List.mem_filter.mp hw).1

def Represents (p : RankInput) (raw : Contracts)
    (R : Finset (Fin p.men.length × Fin p.men.length)) : Prop :=
  ∀ (m w : Fin p.men.length), (m.val, w.val) ∈ raw ↔ (m, w) ∈ R

theorem raw_choice_index {n : Nat} (rows : Rows) (i : Nat) (row : List Nat)
    (hrow : rows.getD i [] = row) (hlen : row.length = n + 1) (hnd : row.Nodup)
    (xs : List Nat) (hx : ∀ j ∈ xs, j < n) :
    rankBest rows i n xs =
      (optionIndex (MathEconLib.Choice.ChoiceFunction.bestOption (rankRowOrder row hlen hnd)
        (boundedFinList xs hx).toFinset)).val := by
  have hscore : rankAt rows i = rankAt [row] 0 := by
    funext j
    unfold rankAt
    rw [hrow]
    rfl
  have h := rankBest_eq_bestOptionIndex row hlen hnd (boundedFinList xs hx)
  rw [boundedFinList_map_val] at h
  have heq : rankBest rows i n xs = rankBest [row] 0 n xs := by
    unfold rankBest
    rw [hscore]
  exact heq.trans h

theorem available_menu (p : RankInput) (raw : Contracts)
    (R : Finset (Fin p.men.length × Fin p.men.length)) (hR : Represents p raw R)
    (m : Fin p.men.length) :
    (boundedFinList (available p.men raw m.val) (available_bounded _ _ _)).toFinset =
      MarriageMarket.partnersMFinset m (Finset.univ \ R) := by
  ext w
  simp only [List.mem_toFinset, mem_boundedFinList, MarriageMarket.mem_partnersMFinset,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  simp [available, participants, hR m w]

theorem proposals_choice (p : RankInput) (raw : Contracts)
    (R : Finset (Fin p.men.length × Fin p.men.length)) (hR : Represents p raw R)
    (m : Fin p.men.length) :
    rankBest p.men m.val p.men.length (available p.men raw m.val) =
      (optionIndex (p.market.bestMFinset m (Finset.univ \ R))).val := by
  have h := raw_choice_index p.men m.val (p.men.get m) (List.getD_eq_get _ _ m)
    (p.men_row_length _ (List.get_mem _ _)) (p.men_row_nodup _ (List.get_mem _ _))
    (available p.men raw m.val) (available_bounded _ _ _)
  rw [available_menu p raw R hR m] at h
  exact h

theorem optionIndex_eq_val_iff {n : Nat} (o : Option (Fin n)) (w : Fin n) :
    (optionIndex o).val = w.val ↔ o = some w := by
  constructor
  · intro h
    exact optionIndex_injective (Fin.ext h)
  · rintro rfl
    rfl

theorem proposals_correct (p : RankInput) (raw : Contracts)
    (R : Finset (Fin p.men.length × Fin p.men.length)) (hR : Represents p raw R) :
    Represents p (proposals p.men raw) (p.market.gsProposalsFinset R) := by
  intro m w
  simp only [proposals, List.mem_filter, mem_pairs, beq_iff_eq,
    Fin.is_lt, true_and, MarriageMarket.gsProposalsFinset, Finset.mem_filter,
    Finset.mem_univ]
  rw [proposals_choice p raw R hR m, optionIndex_eq_val_iff]
  exact eq_comm

theorem proposals_bounded (rows : Rows) (raw : Contracts) :
    ∀ q ∈ proposals rows raw, q.1 < rows.length ∧ q.2 < rows.length := by
  intro q hq
  exact (mem_pairs rows q).mp (List.mem_filter.mp hq).1

theorem suitors_bounded {n : Nat} (raw : Contracts)
    (hb : ∀ q ∈ raw, q.1 < n ∧ q.2 < n) (w : Nat) :
    ∀ m ∈ suitors raw w, m < n := by
  intro m hm
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
  exact (hb q (List.mem_filter.mp hq).1).1

theorem suitors_menu (p : RankInput) (raw : Contracts)
    (P : Finset (Fin p.men.length × Fin p.men.length)) (hP : Represents p raw P)
    (hb : ∀ q ∈ raw, q.1 < p.men.length ∧ q.2 < p.men.length)
    (w : Fin p.men.length) :
    (boundedFinList (suitors raw w.val) (suitors_bounded raw hb _)).toFinset =
      MarriageMarket.partnersWFinset w P := by
  ext m
  simp only [List.mem_toFinset, mem_boundedFinList, MarriageMarket.mem_partnersWFinset]
  constructor
  · intro hm
    obtain ⟨⟨i, j⟩, hij, hi⟩ := List.mem_map.mp hm
    obtain ⟨hraw, hj⟩ := List.mem_filter.mp hij
    simp only [beq_iff_eq] at hj
    dsimp only at hi hj
    subst i
    subst j
    exact (hP m w).mp hraw
  · intro hm
    exact List.mem_map.mpr ⟨(m.val, w.val),
      List.mem_filter.mpr ⟨(hP m w).mpr hm, by simp⟩, rfl⟩

theorem held_choice (p : RankInput) (raw : Contracts)
    (P : Finset (Fin p.men.length × Fin p.men.length)) (hP : Represents p raw P)
    (hb : ∀ q ∈ raw, q.1 < p.men.length ∧ q.2 < p.men.length)
    (w : Fin p.men.length) :
    rankBest p.women w.val p.men.length (suitors raw w.val) =
      (optionIndex (p.market.bestWFinset w P)).val := by
  let i : Fin p.women.length := Fin.cast p.women_length.symm w
  have h := raw_choice_index p.women w.val (p.women.get i) (List.getD_eq_get _ _ i)
    (p.women_row_length _ (List.get_mem _ _)) (p.women_row_nodup _ (List.get_mem _ _))
    (suitors raw w.val) (suitors_bounded raw hb _)
  rw [suitors_menu p raw P hP hb w] at h
  exact h

theorem held_correct (p : RankInput) (raw : Contracts)
    (P : Finset (Fin p.men.length × Fin p.men.length)) (hP : Represents p raw P)
    (hb : ∀ q ∈ raw, q.1 < p.men.length ∧ q.2 < p.men.length) :
    Represents p (held p.women p.men.length raw) (p.market.gsHoldProposalsFinset P) := by
  intro m w
  simp only [held, List.mem_filter, beq_iff_eq, MarriageMarket.gsHoldProposalsFinset,
    Finset.mem_filter]
  rw [hP m w, held_choice p raw P hP hb w, optionIndex_eq_val_iff]
  exact and_congr_right (fun _ => eq_comm)

theorem step_correct (p : RankInput) (raw : Contracts)
    (R : Finset (Fin p.men.length × Fin p.men.length)) (hR : Represents p raw R) :
    Represents p (step (p.men, p.women) raw) (p.market.gsStepFinset R) := by
  intro m w
  have hP := proposals_correct p raw R hR
  have hH := held_correct p (proposals p.men raw) (p.market.gsProposalsFinset R) hP
    (proposals_bounded p.men raw)
  simp [step, mem_pairs, hR m w, hP m w, hH m w, MarriageMarket.gsStepFinset]

theorem iterate_correct {α : Type} (p : RankInput) (fuel : List α) (raw : Contracts)
    (R : Finset (Fin p.men.length × Fin p.men.length)) (hR : Represents p raw R) :
    Represents p (fuel.foldl (fun raw _ => step (p.men, p.women) raw) raw)
      ((p.market.gsStepFinset)^[fuel.length] R) := by
  induction fuel generalizing raw R with
  | nil => exact hR
  | cons x fuel ih =>
    simpa only [List.foldl_cons, List.length_cons, Function.iterate_succ_apply] using
      ih (step (p.men, p.women) raw) (p.market.gsStepFinset R) (step_correct p raw R hR)

theorem pairs_length (rows : Rows) : (pairs rows).length = rows.length * rows.length := by
  change ((List.range rows.length) ×ˢ (List.range rows.length)).length = _
  simp only [List.length_product, List.length_range]

theorem rejected_correct (p : RankInput) :
    Represents p (rejected (p.men, p.women))
      (p.market.gsRejectedFinset (p.men.length * p.men.length)) := by
  have h := iterate_correct p (pairs p.men) [] ∅ (by simp [Represents])
  simpa only [rejected, pairs_length, MarriageMarket.gsRejectedFinset] using h

theorem output_correct (p : RankInput) :
    Represents p (output (p.men, p.women)) p.market.galeShapleyFinset := by
  have hP := proposals_correct p (rejected (p.men, p.women)) _ (rejected_correct p)
  have hH := held_correct p _ _ hP (proposals_bounded _ _)
  simpa only [output, MarriageMarket.galeShapleyFinset,
    MarriageMarket.galeShapleyFinsetWithFuel, MarriageMarket.gsHeldFinset,
    Fintype.card_prod, Fintype.card_fin] using hH

theorem output_matching (p : RankInput) (m w : Fin p.men.length) :
    (m.val, w.val) ∈ output (p.men, p.women) ↔
      p.market.galeShapleyComputable m = some w := by
  rw [output_correct p m w]
  change (m, w) ∈ (p.market.galeShapleyFinset : Set _) ↔ _
  rw [p.market.galeShapleyFinset_eq_graphOf_galeShapleyComputable]
  rfl

end StableMatching.RankDA
