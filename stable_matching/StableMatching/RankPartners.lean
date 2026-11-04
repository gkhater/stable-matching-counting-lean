import StableMatching.RankThreshold

/-! Canonical partner vectors computed from the costed DA contract lists. -/

namespace StableMatching.RankDA

open MathEconLib.Matching
open MathEconLib.Matching.MarriageMarket
open Groundwork
open RankInputComplexity

def partnerCode (n : Nat) (raw : Contracts) (m : Nat) : Nat :=
  ((raw.find? (fun p => p.1 == m)).map Prod.snd).getD n

def partnerCodes (rows : Rows) (raw : Contracts) : List Nat :=
  (participants rows).map (fun m => partnerCode rows.length raw m)

def matchingCodes {n : Nat} (μ : Fin n ≃. Fin n) : List Nat :=
  (List.finRange n).map (fun m => (optionIndex (μ m)).val)

@[fun_prop] theorem partnerCode_polyT {α : Type} [Enc α]
    {n m : α → Nat} {raw : α → Contracts}
    (hn : PolyT n) (hm : PolyT m) (hraw : PolyT raw) :
    PolyT (fun x => partnerCode (n x) (raw x) (m x)) := by
  unfold partnerCode
  fun_prop

@[fun_prop] theorem partnerCodes_polyT {α : Type} [Enc α]
    {rows : α → Rows} {raw : α → Contracts} (hrows : PolyT rows) (hraw : PolyT raw) :
    PolyT (fun x => partnerCodes (rows x) (raw x)) := by
  unfold partnerCodes
  fun_prop

@[simp] theorem partnerCodes_length (rows : Rows) (raw : Contracts) :
    (partnerCodes rows raw).length = rows.length := by simp [partnerCodes, participants]

@[simp] theorem matchingCodes_length {n : Nat} (μ : Fin n ≃. Fin n) :
    (matchingCodes μ).length = n := by simp [matchingCodes]

theorem partnerCodes_getD (rows : Rows) (raw : Contracts) (i : Nat)
    (hi : i < rows.length) (d : Nat) :
    (partnerCodes rows raw).getD i d = partnerCode rows.length raw i := by
  rw [List.getD_eq_getElem _ d (by simpa using hi)]
  simp [partnerCodes, participants]

theorem matchingCodes_getD {n : Nat} (μ : Fin n ≃. Fin n) (i : Fin n) (d : Nat) :
    (matchingCodes μ).getD i.val d = (optionIndex (μ i)).val := by
  rw [List.getD_eq_getElem _ d (by simp)]
  simp only [matchingCodes, List.getElem_map, List.getElem_finRange]
  rfl

theorem matchingCodes_injective {n : Nat} : Function.Injective (@matchingCodes n) := by
  intro μ ν h
  apply PEquiv.ext
  intro i
  apply optionIndex_injective
  apply Fin.ext
  have hget := congrArg (fun xs : List Nat => xs.getD i.val n) h
  simpa only [matchingCodes_getD] using hget

theorem optionIndex_eq_n_iff {n : Nat} (o : Option (Fin n)) :
    (optionIndex o).val = n ↔ o = none := by
  cases o with
  | none => simp [optionIndex]
  | some w =>
    have := w.is_lt
    simp only [optionIndex, Fin.val_castSucc, Option.some_ne_none, iff_false]
    omega

theorem partnerCode_correct {n : Nat} (raw : Contracts) (μ : Fin n ≃. Fin n)
    (hb : ∀ q ∈ raw, q.1 < n ∧ q.2 < n)
    (hμ : ∀ i w : Fin n, (i.val, w.val) ∈ raw ↔ μ i = some w) (i : Fin n) :
    partnerCode n raw i.val = (optionIndex (μ i)).val := by
  unfold partnerCode
  cases hfind : raw.find? (fun p => p.1 == i.val) with
  | none =>
    have hnone : μ i = none := by
      cases hi : μ i with
      | none => rfl
      | some w =>
        have hm := (hμ i w).mpr hi
        have hf := (List.find?_eq_none.mp hfind) (i.val, w.val) hm
        simp at hf
    simp only [Option.map_none, Option.getD_none, hnone, optionIndex]
  | some q =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hpred : (q.1 == i.val) = true :=
      List.find?_some (p := fun p : Nat × Nat => p.1 == i.val) hfind
    have hfirst : q.1 = i.val := beq_iff_eq.mp hpred
    let w : Fin n := ⟨q.2, (hb q hmem).2⟩
    have hraw : (i.val, w.val) ∈ raw := by simpa only [w, ← hfirst, Prod.mk.eta] using hmem
    have hi := (hμ i w).mp hraw
    simp only [Option.map_some, Option.getD_some, hi, optionIndex, Fin.val_castSucc]
    rfl

theorem partnerCodes_correct {n : Nat} (rows : Rows) (hlen : rows.length = n)
    (raw : Contracts) (μ : Fin n ≃. Fin n)
    (hb : ∀ q ∈ raw, q.1 < n ∧ q.2 < n)
    (hμ : ∀ i w : Fin n, (i.val, w.val) ∈ raw ↔ μ i = some w) :
    partnerCodes rows raw = matchingCodes μ := by
  apply List.ext_getElem
  · simp [hlen]
  · intro j hj hk
    have hjn : j < n := by simpa using hk
    have hjr : j < rows.length := by omega
    let i : Fin n := ⟨j, hjn⟩
    have h := partnerCode_correct raw μ hb hμ i
    have hleft := partnerCodes_getD rows raw j hjr n
    have hright := matchingCodes_getD μ i n
    rw [hlen] at hleft
    rw [← hleft, ← hright] at h
    rw [List.getD_eq_getElem _ n hj, List.getD_eq_getElem _ n hk] at h
    exact h

theorem output_bounded (input : Input) :
    ∀ q ∈ output input, q.1 < input.1.length ∧ q.2 < input.1.length := by
  intro q hq
  exact proposals_bounded _ _ q (List.mem_filter.mp hq).1

theorem woman_output_bounded (p : RankInput) :
    ∀ q ∈ womanOutput (p.men, p.women), q.1 < p.men.length ∧ q.2 < p.men.length := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  have hb := output_bounded (p.women, p.men) r hr
  change r.2 < p.men.length ∧ r.1 < p.men.length
  simpa only [p.women_length] using And.intro hb.2 hb.1

theorem threshold_output_bounded (p : RankInput) (m t : Fin p.men.length) :
    ∀ q ∈ thresholdOutput (p.men, p.women) m.val t.val,
      q.1 < p.men.length ∧ q.2 < p.men.length := by
  change ∀ q ∈ womanOutput (truncateRankRows p.men m.val t.val, p.women),
    q.1 < p.men.length ∧ q.2 < p.men.length
  simpa only [p.truncated_length m t] using woman_output_bounded (p.truncated m t)

end StableMatching.RankDA
