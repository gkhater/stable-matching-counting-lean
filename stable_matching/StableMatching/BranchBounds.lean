import StableMatching.BranchTree
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reciprocal-potential depth bound for stopped branching

The only quantitative input is a lower bound on the two cones of each selected
pivot. The tree itself is the computed `BranchTree.build`. Thin-chain centrality
will discharge the quantitative input for the computed matching poset.
-/

namespace StableMatching.BranchTree

theorem reciprocal_increase {A q next : ℝ} (hA : 0 < A) (hq : 0 < q)
    (hnext : 0 < next) (hle : next ≤ q) (hdrop : q ^ 2 ≤ A * (q - next)) :
    1 + A / q ≤ A / next := by
  have hproduct : q * next ≤ A * (q - next) := by
    calc
      q * next ≤ q * q := mul_le_mul_of_nonneg_left hle hq.le
      _ = q ^ 2 := (pow_two q).symm
      _ ≤ A * (q - next) := hdrop
  have hidentity : A / next - A / q = A * (q - next) / (q * next) := by
    field_simp [ne_of_gt hq, ne_of_gt hnext]
  have hstep : 1 ≤ A * (q - next) / (q * next) :=
    (le_div_iff₀ (mul_pos hq hnext)).mpr (by simpa using hproduct)
  rw [← hidentity] at hstep
  linarith

variable {P : Type*} [Preorder P] [DecidableLE P]

theorem Valid.height_eq_zero_of_length_le {cutoff : Nat} {remaining : List P} {tree : Tree P}
    (h : Valid cutoff remaining tree) (hsmall : remaining.length ≤ cutoff) : tree.height = 0 := by
  cases h with
  | leaf => rfl
  | node hcontinue => omega

/-- The reciprocal potential gains at least one per continuing branch. -/
theorem Valid.height_lt_potential {cutoff : Nat} {A : ℝ}
    (hcutoff : 0 < cutoff) (hA : 0 < A)
    (hcenter : ∀ (remaining : List P), remaining.Nodup → cutoff < remaining.length →
      ∀ pivot ∈ remaining,
        (∀ x ∈ remaining, score remaining x ≤ score remaining pivot) →
        (remaining.length : ℝ) ^ 2 ≤ A * (score remaining pivot : ℝ))
    {remaining : List P} {tree : Tree P} (h : Valid cutoff remaining tree) :
    remaining.Nodup → cutoff < remaining.length →
      (tree.height : ℝ) < 1 + A / (cutoff : ℝ) - A / (remaining.length : ℝ) := by
  induction h with
  | leaf remaining hstop =>
      intro _ hcontinue
      omega
  | @node remaining pivot left right hcontinue hp hmax hleft hright ihleft ihright =>
      intro hnodup _
      have hc : (0 : ℝ) < cutoff := by exact_mod_cast hcutoff
      have hq : (0 : ℝ) < remaining.length := by exact_mod_cast (hcutoff.trans hcontinue)
      have hcq : (cutoff : ℝ) < remaining.length := by exact_mod_cast hcontinue
      have hcentral := hcenter remaining hnodup hcontinue pivot hp hmax
      have hscoreDown : (score remaining pivot : ℝ) ≤ downSize remaining pivot := by
        exact_mod_cast (Nat.min_le_left (downSize remaining pivot) (upSize remaining pivot))
      have hscoreUp : (score remaining pivot : ℝ) ≤ upSize remaining pivot := by
        exact_mod_cast (Nat.min_le_right (downSize remaining pivot) (upSize remaining pivot))
      have hincsum : ((includeResidual remaining pivot).length : ℝ) + downSize remaining pivot =
          remaining.length := by exact_mod_cast includeResidual_length_add_downSize remaining pivot
      have hexcsum : ((excludeResidual remaining pivot).length : ℝ) + upSize remaining pivot =
          remaining.length := by exact_mod_cast excludeResidual_length_add_upSize remaining pivot
      have hincdrop : (remaining.length : ℝ) ^ 2 ≤
          A * ((remaining.length : ℝ) - (includeResidual remaining pivot).length) := by
        have hdown : (downSize remaining pivot : ℝ) =
            (remaining.length : ℝ) - (includeResidual remaining pivot).length := by linarith
        rw [← hdown]
        exact hcentral.trans (mul_le_mul_of_nonneg_left hscoreDown hA.le)
      have hexcdrop : (remaining.length : ℝ) ^ 2 ≤
          A * ((remaining.length : ℝ) - (excludeResidual remaining pivot).length) := by
        have hup : (upSize remaining pivot : ℝ) =
            (remaining.length : ℝ) - (excludeResidual remaining pivot).length := by linarith
        rw [← hup]
        exact hcentral.trans (mul_le_mul_of_nonneg_left hscoreUp hA.le)
      have hfrac : A / (remaining.length : ℝ) < A / (cutoff : ℝ) := by
        apply (div_lt_div_iff₀ hq hc).mpr
        exact mul_lt_mul_of_pos_left hcq hA
      have hl : 1 + (left.height : ℝ) <
          1 + A / (cutoff : ℝ) - A / (remaining.length : ℝ) := by
        by_cases hsmall : (includeResidual remaining pivot).length ≤ cutoff
        · rw [hleft.height_eq_zero_of_length_le hsmall]
          norm_num
          linarith
        · have hcont : cutoff < (includeResidual remaining pivot).length := Nat.lt_of_not_ge hsmall
          have hchildpos : (0 : ℝ) < (includeResidual remaining pivot).length := by
            exact_mod_cast (hcutoff.trans hcont)
          have hchildle : ((includeResidual remaining pivot).length : ℝ) ≤ remaining.length := by
            exact_mod_cast (includeResidual_length_lt remaining pivot hp).le
          have hstep := reciprocal_increase hA hq hchildpos hchildle hincdrop
          have hchild := ihleft (hnodup.filter _) hcont
          linarith
      have hr : 1 + (right.height : ℝ) <
          1 + A / (cutoff : ℝ) - A / (remaining.length : ℝ) := by
        by_cases hsmall : (excludeResidual remaining pivot).length ≤ cutoff
        · rw [hright.height_eq_zero_of_length_le hsmall]
          norm_num
          linarith
        · have hcont : cutoff < (excludeResidual remaining pivot).length := Nat.lt_of_not_ge hsmall
          have hchildpos : (0 : ℝ) < (excludeResidual remaining pivot).length := by
            exact_mod_cast (hcutoff.trans hcont)
          have hchildle : ((excludeResidual remaining pivot).length : ℝ) ≤ remaining.length := by
            exact_mod_cast (excludeResidual_length_lt remaining pivot hp).le
          have hstep := reciprocal_increase hA hq hchildpos hchildle hexcdrop
          have hchild := ihright (hnodup.filter _) hcont
          linarith
      simpa only [Tree.height, Nat.cast_add, Nat.cast_one, Nat.cast_max, add_max] using
        (max_lt_iff.mpr ⟨hl, hr⟩)

theorem Valid.height_lt_bound {cutoff : Nat} {A : ℝ}
    (hcutoff : 0 < cutoff) (hA : 0 < A)
    (hcenter : ∀ (remaining : List P), remaining.Nodup → cutoff < remaining.length →
      ∀ pivot ∈ remaining,
        (∀ x ∈ remaining, score remaining x ≤ score remaining pivot) →
        (remaining.length : ℝ) ^ 2 ≤ A * (score remaining pivot : ℝ))
    {remaining : List P} {tree : Tree P} (h : Valid cutoff remaining tree)
    (hnodup : remaining.Nodup) : (tree.height : ℝ) < 1 + A / (cutoff : ℝ) := by
  by_cases hsmall : remaining.length ≤ cutoff
  · rw [h.height_eq_zero_of_length_le hsmall]
    have hc : (0 : ℝ) < cutoff := by exact_mod_cast hcutoff
    have hnonneg : 0 ≤ A / (cutoff : ℝ) := (div_pos hA hc).le
    norm_num
    linarith
  · have hpotential := h.height_lt_potential hcutoff hA hcenter hnodup (Nat.lt_of_not_ge hsmall)
    have hnonneg : 0 ≤ A / (remaining.length : ℝ) := div_nonneg hA.le (by positivity)
    linarith

theorem Valid.leaf_bound {cutoff H : Nat} {A : ℝ}
    (hcutoff : 0 < cutoff) (hA : 0 < A)
    (hcenter : ∀ (remaining : List P), remaining.Nodup → cutoff < remaining.length →
      ∀ pivot ∈ remaining,
        (∀ x ∈ remaining, score remaining x ≤ score remaining pivot) →
        (remaining.length : ℝ) ^ 2 ≤ A * (score remaining pivot : ℝ))
    {remaining : List P} {tree : Tree P} (h : Valid cutoff remaining tree)
    (hnodup : remaining.Nodup) (hH : 1 + A / (cutoff : ℝ) ≤ H) :
    tree.leaves.length ≤ 2 ^ H := by
  have hheight : (tree.height : ℝ) < H :=
    (h.height_lt_bound hcutoff hA hcenter hnodup).trans_le hH
  have hnat : tree.height ≤ H := by exact_mod_cast hheight.le
  exact tree.leaves_length_le_pow_height.trans (Nat.pow_le_pow_right (by decide) hnat)

end StableMatching.BranchTree
