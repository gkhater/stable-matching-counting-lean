import StableMatching.BranchBounds
import StableMatching.ResidualEncoding
import MathEconLib.ForMathlib.Order.ThinChains.Pivot

/-! Thin-chain centrality discharges the quantitative premise of the actual
maximal-cone branching algorithm. In particular the pivot is computed by
`argmax`; no central element is provided to the algorithm as an input. -/

namespace StableMatching.ThinBranching

open MathEconLib.Order

variable {P R C : Type*} [PartialOrder P] [Fintype P] [Fintype R] [Fintype C]
variable [DecidableLE P] [DecidableEq P]

omit [Fintype P] [DecidableLE P] in
theorem card_membership (remaining : List P) (hnodup : remaining.Nodup) :
    Nat.card {x : P // x ∈ remaining} = remaining.length := by
  have h := Nat.card_congr (ResidualEncoding.indexOrderIso remaining hnodup).toEquiv
  simpa only [Nat.card_fin] using h.symm

def downConeEquiv (remaining : List P) (pivot : P) :
    {y : {x : P // x ∈ remaining} // y.1 ≤ pivot} ≃
      {y : P // y ∈ remaining.filter (fun x => decide (x ≤ pivot))} where
  toFun y := ⟨y.1.1, List.mem_filter.mpr ⟨y.1.2, by simpa using y.2⟩⟩
  invFun y := ⟨⟨y.1, (List.mem_filter.mp y.2).1⟩, by
    simpa using (List.mem_filter.mp y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def upConeEquiv (remaining : List P) (pivot : P) :
    {y : {x : P // x ∈ remaining} // pivot ≤ y.1} ≃
      {y : P // y ∈ remaining.filter (fun x => decide (pivot ≤ x))} where
  toFun y := ⟨y.1.1, List.mem_filter.mpr ⟨y.1.2, by simpa using y.2⟩⟩
  invFun y := ⟨⟨y.1, (List.mem_filter.mp y.2).1⟩, by
    simpa using (List.mem_filter.mp y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype P] in
theorem downSize_eq_card (remaining : List P) (hnodup : remaining.Nodup)
    (pivot : P) (hp : pivot ∈ remaining) :
    BranchTree.downSize remaining pivot =
      Nat.card {y : {x : P // x ∈ remaining} // y ≤ (⟨pivot, hp⟩ : {x : P // x ∈ remaining})} := by
  exact (card_membership _ (hnodup.filter _)).symm.trans
    (Nat.card_congr (downConeEquiv remaining pivot)).symm

omit [Fintype P] in
theorem upSize_eq_card (remaining : List P) (hnodup : remaining.Nodup)
    (pivot : P) (hp : pivot ∈ remaining) :
    BranchTree.upSize remaining pivot =
      Nat.card {y : {x : P // x ∈ remaining} // (⟨pivot, hp⟩ : {x : P // x ∈ remaining}) ≤ y} := by
  exact (card_membership _ (hnodup.filter _)).symm.trans
    (Nat.card_congr (upConeEquiv remaining pivot)).symm

omit [Fintype P] in
theorem selected_pivot_bound (t : ThinChains P R C) (remaining : List P)
    (hnodup : remaining.Nodup) (pivot : P) (hp : pivot ∈ remaining)
    (hmax : ∀ x ∈ remaining, BranchTree.score remaining x ≤ BranchTree.score remaining pivot) :
    remaining.length ^ 2 ≤ 8 * Fintype.card R * Fintype.card C * BranchTree.score remaining pivot := by
  classical
  let : Nonempty {x : P // x ∈ remaining} := ⟨⟨pivot, hp⟩⟩
  obtain ⟨x, hx⟩ := (t.restrict (fun x => x ∈ remaining)).exists_central_pivot
  have hcard : Fintype.card {x : P // x ∈ remaining} = remaining.length := by
    rw [← Nat.card_eq_fintype_card]
    exact card_membership remaining hnodup
  rw [hcard, ← downSize_eq_card remaining hnodup x.1 x.2,
    ← upSize_eq_card remaining hnodup x.1 x.2] at hx
  exact hx.trans (Nat.mul_le_mul_left _ (hmax x.1 x.2))

theorem build_height_bound (t : ThinChains P R C) (cutoff : Nat) (hcutoff : 0 < cutoff)
    (harea : 0 < Fintype.card R * Fintype.card C)
    (remaining : List P) (hnodup : remaining.Nodup) :
    ((BranchTree.build cutoff remaining).1.height : ℝ) <
      1 + (8 * Fintype.card R * Fintype.card C : ℝ) / (cutoff : ℝ) := by
  have hA : (0 : ℝ) < 8 * Fintype.card R * Fintype.card C := by
    have hnat : 0 < 8 * Fintype.card R * Fintype.card C := by
      simpa only [mul_assoc] using Nat.mul_pos (by decide : 0 < 8) harea
    exact_mod_cast hnat
  apply (BranchTree.build cutoff remaining).2.height_lt_bound hcutoff hA _ hnodup
  intro residual hresidual _ pivot hp hmax
  exact_mod_cast selected_pivot_bound t residual hresidual pivot hp hmax

theorem reduce_query_bound (t : ThinChains P R C) (cutoff H : Nat) (hcutoff : 0 < cutoff)
    (harea : 0 < Fintype.card R * Fintype.card C)
    (hH : 1 + (8 * Fintype.card R * Fintype.card C : ℝ) / (cutoff : ℝ) ≤ H)
    (remaining : List P) (hnodup : remaining.Nodup) :
    (ResidualEncoding.reduce cutoff remaining).length ≤ 2 ^ H := by
  have hheight := build_height_bound t cutoff hcutoff harea remaining hnodup
  have hnat : (BranchTree.build cutoff remaining).1.height ≤ H := by
    exact_mod_cast (hheight.trans_le hH).le
  simpa only [ResidualEncoding.reduce, List.length_map] using
    (BranchTree.build cutoff remaining).1.leaves_length_le_pow_height.trans
      (Nat.pow_le_pow_right (by decide) hnat)

end StableMatching.ThinBranching
