import StableMatching.RateTradeoff
import StableMatching.CompactSize
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# An explicit growing block schedule

The schedule uses the fourth root of the binary logarithm of the market
size, rounded down. Its bit width is the least width that represents every
cut in such a block.
-/

namespace StableMatching.LogarithmicRate

open MainTheoremForms

noncomputable def logScale (n : Nat) : ℝ := lg ((n : ℝ) + 4)

noncomputable def rootScale (n : Nat) : ℝ := (logScale n) ^ (1 / 4 : ℝ)

noncomputable def blockLength (n : Nat) : Nat := max 1 ⌊rootScale n⌋₊

noncomputable def bitWidth (n : Nat) : Nat := CompactSize.bitWidth (blockLength n)

theorem logScale_ge_two (n : Nat) : 2 ≤ logScale n := by
  exact (Wrap.Arith.lg_add_four_facts n).1

theorem rootScale_ge_one (n : Nat) : 1 ≤ rootScale n := by
  exact Real.one_le_rpow (by have := logScale_ge_two n; linarith) (by norm_num)

theorem blockLength_pos (n : Nat) : 0 < blockLength n := by
  simp [blockLength]

theorem bitWidth_pos (n : Nat) : 0 < bitWidth n := by
  exact CompactSize.bitWidth_pos (blockLength_pos n)

theorem bitWidth_capacity (n : Nat) : blockLength n + 1 ≤ 2 ^ bitWidth n := by
  exact CompactSize.bitWidth_capacity (blockLength n)

theorem bitWidth_pow_le_twice (n : Nat) :
    2 ^ bitWidth n ≤ 2 * (blockLength n + 1) := by
  exact CompactSize.bitWidth_pow_le_twice (blockLength_pos n)

theorem blockLength_le_rootScale (n : Nat) :
    (blockLength n : ℝ) ≤ rootScale n := by
  have hfloor : 1 ≤ ⌊rootScale n⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (rootScale_ge_one n)
  have heq : blockLength n = ⌊rootScale n⌋₊ := by
    simp [blockLength, max_eq_right hfloor]
  rw [heq]
  exact Nat.floor_le (by have := rootScale_ge_one n; linarith)

theorem rootScale_le_logScale (n : Nat) :
    rootScale n ≤ logScale n := by
  exact Real.rpow_le_self_of_one_le
    (by have := logScale_ge_two n; linarith) (by norm_num)

theorem clog_le_log_add_one (x : Nat) :
    Nat.clog 2 x ≤ Nat.log 2 x + 1 := by
  apply Nat.clog_le_of_le_pow
  exact (Nat.lt_pow_succ_log_self Nat.one_lt_two x).le

theorem natLog_le_lg {x : Nat} (hx : 0 < x) :
    (Nat.log 2 x : ℝ) ≤ lg (x : ℝ) := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hx)).mpr
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hx)

/-- The binary width is controlled by the real logarithm of the number of
possible cut values. -/
theorem bitWidth_le_lg (n : Nat) :
    (bitWidth n : ℝ) ≤ 1 + lg ((blockLength n + 1 : Nat) : ℝ) := by
  have hnat := clog_le_log_add_one (blockLength n + 1)
  have hlog := natLog_le_lg (by omega : 0 < blockLength n + 1)
  have hreal : (Nat.clog 2 (blockLength n + 1) : ℝ) ≤
      (Nat.log 2 (blockLength n + 1) : ℝ) + 1 := by exact_mod_cast hnat
  dsimp [bitWidth, CompactSize.bitWidth]
  linarith

/-- A uniform small-power bound on the binary logarithm. -/
theorem lg_le_sixteenth_root {x : ℝ} (hx : 1 ≤ x) :
    lg x ≤ 32 * x ^ (1 / 16 : ℝ) := by
  have hpow : 0 ≤ x ^ (1 / 16 : ℝ) := by positivity
  have hraw := Real.log_le_rpow_div (by linarith : 0 ≤ x)
    (by norm_num : (0 : ℝ) < 1 / 16)
  have hln : (1 : ℝ) / 2 < Real.log 2 := Wrap.Arith.half_lt_log_two
  unfold lg Real.logb
  apply (div_le_iff₀ (by linarith)).mpr
  norm_num at hraw ⊢
  nlinarith

theorem logScale_le_linear (n : Nat) :
    logScale n ≤ 2 * (n : ℝ) + 6 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h := Wrap.Arith.lg_le_two_mul_sub
    (show (1 : ℝ) ≤ (n : ℝ) + 4 by linarith)
  dsimp [logScale]
  linarith

theorem bitWidth_le_linear (n : Nat) :
    (bitWidth n : ℝ) ≤ 2 * (n : ℝ) + 7 := by
  have hbits := CompactSize.bitWidth_le (blockLength n)
  have hbitsR : (bitWidth n : ℝ) ≤ (blockLength n : ℝ) + 1 := by
    exact_mod_cast hbits
  linarith [blockLength_le_rootScale n, rootScale_le_logScale n,
    logScale_le_linear n]

/-- The prepared query's logarithm is at most four times the market-size
logarithm. This deliberately uses a coarse polynomial bound on the width. -/
theorem query_logScale_le (n : Nat) :
    lg ((((2 * n * bitWidth n : Nat) : ℝ) + 4)) ≤ 4 * logScale n := by
  let X : ℝ := (n : ℝ) + 4
  have hX : 0 < X := by dsimp [X]; positivity
  have hmul := mul_le_mul_of_nonneg_left (bitWidth_le_linear n)
    (show (0 : ℝ) ≤ 2 * n by positivity)
  have harg : (((2 * n * bitWidth n : Nat) : ℝ) + 4) ≤ 4 * X ^ 2 := by
    dsimp [X]
    push_cast
    nlinarith
  have hmono := VariableBound.Paper.lg_mono
    (show 0 < (((2 * n * bitWidth n : Nat) : ℝ) + 4) by positivity) harg
  have hlg4 : lg (4 : ℝ) = 2 := by
    unfold lg
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hpow : lg (X ^ 2) = 2 * lg X := Real.logb_pow 2 X 2
  have heq : lg (4 * X ^ 2) = 2 + 2 * logScale n := by
    unfold logScale lg at *
    rw [Real.logb_mul (by norm_num : (4 : ℝ) ≠ 0)
      (by positivity : X ^ 2 ≠ 0), Real.logb_pow]
    exact congrArg (fun t : ℝ => t + 2 * Real.logb 2 X) hlg4
  rw [heq] at hmono
  have hΛ := logScale_ge_two n
  linarith

theorem add_one_rpow_le_twice (n : Nat) :
    (logScale n + 1) ^ (1 / 16 : ℝ) ≤
      2 * (logScale n) ^ (1 / 16 : ℝ) := by
  have hΛ := logScale_ge_two n
  have hpow : 0 ≤ (logScale n) ^ (1 / 16 : ℝ) := by positivity
  calc
    (logScale n + 1) ^ (1 / 16 : ℝ) ≤
        (2 * logScale n) ^ (1 / 16 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    _ = 2 ^ (1 / 16 : ℝ) * (logScale n) ^ (1 / 16 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
    _ ≤ 2 * (logScale n) ^ (1 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) hpow

/-- Three factors of the bit width can be paid for with a small power of
the main logarithm. -/
theorem bitWidth_le_sixteenth_root (n : Nat) :
    (bitWidth n : ℝ) ≤ 65 * (logScale n) ^ (1 / 16 : ℝ) := by
  have harg : (((blockLength n + 1 : Nat) : ℝ)) ≤ logScale n + 1 := by
    push_cast
    linarith [blockLength_le_rootScale n, rootScale_le_logScale n]
  have hmono := VariableBound.Paper.lg_mono
    (show 0 < (((blockLength n + 1 : Nat) : ℝ)) by positivity) harg
  have hlog := lg_le_sixteenth_root
    (show (1 : ℝ) ≤ logScale n + 1 by linarith [logScale_ge_two n])
  have hpow : 1 ≤ (logScale n) ^ (1 / 16 : ℝ) :=
    Real.one_le_rpow (by linarith [logScale_ge_two n]) (by norm_num)
  have htwice := add_one_rpow_le_twice n
  linarith [bitWidth_le_lg n]

theorem logScale_le_query_logScale (n : Nat) :
    logScale n ≤ lg ((((2 * n * bitWidth n : Nat) : ℝ) + 4)) := by
  have hmul : n ≤ 2 * n * bitWidth n := by
    calc
      n = n * 1 := by omega
      _ ≤ n * (2 * bitWidth n) :=
        Nat.mul_le_mul_left n (by have := bitWidth_pos n; omega : 1 ≤ 2 * bitWidth n)
      _ = 2 * n * bitWidth n := by ring
  have harg : (n : ℝ) + 4 ≤ (((2 * n * bitWidth n : Nat) : ℝ) + 4) := by
    exact_mod_cast Nat.add_le_add_right hmul 4
  exact VariableBound.Paper.lg_mono (by positivity) harg

theorem query_loglog_le_sixteenth_root (n : Nat) :
    lg (lg ((((2 * n * bitWidth n : Nat) : ℝ) + 4))) ≤
      34 * (logScale n) ^ (1 / 16 : ℝ) := by
  have hlgq := (Wrap.Arith.lg_add_four_facts (2 * n * bitWidth n)).1
  have hmono := VariableBound.Paper.lg_mono
    (by linarith : 0 < lg ((((2 * n * bitWidth n : Nat) : ℝ) + 4)))
    (query_logScale_le n)
  have hΛ := logScale_ge_two n
  have hlg4 : lg (4 : ℝ) = 2 := by
    unfold lg
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have heq : lg (4 * logScale n) = 2 + lg (logScale n) := by
    unfold lg at hlg4 ⊢
    rw [Real.logb_mul (by norm_num : (4 : ℝ) ≠ 0)
      (by linarith : logScale n ≠ 0), hlg4]
  rw [heq] at hmono
  have hlog := lg_le_sixteenth_root (by linarith : 1 ≤ logScale n)
  have hpow : 1 ≤ (logScale n) ^ (1 / 16 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  linarith

/-- The SAT variable rate at the scheduled width has the expected
one-half-log denominator, with only a small-power numerator. -/
theorem query_rate_le (n : Nat) :
    SatK.rN 1 (1 / 2) (2 * n * bitWidth n) ≤
      (34 * (logScale n) ^ (1 / 16 : ℝ)) / Real.sqrt (logScale n) := by
  have hΛ := logScale_ge_two n
  have hquery := logScale_le_query_logScale n
  have hroot := Real.sqrt_le_sqrt hquery
  have hrootPos : 0 < Real.sqrt (logScale n) :=
    Real.sqrt_pos.mpr (by linarith)
  have hnum0 : 0 ≤ lg (lg ((((2 * n * bitWidth n : Nat) : ℝ) + 4))) := by
    have h := (Wrap.Arith.lg_add_four_facts (2 * n * bitWidth n)).2
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) h
  rw [Wrap.Arith.rate_eq]
  calc
    lg (lg (((2 * n * bitWidth n : Nat) : ℝ) + 4)) /
        Real.sqrt (lg (((2 * n * bitWidth n : Nat) : ℝ) + 4)) ≤
      lg (lg (((2 * n * bitWidth n : Nat) : ℝ) + 4)) /
        Real.sqrt (logScale n) :=
      div_le_div_of_nonneg_left hnum0 hrootPos hroot
    _ ≤ (34 * (logScale n) ^ (1 / 16 : ℝ)) / Real.sqrt (logScale n) :=
      div_le_div_of_nonneg_right (query_loglog_le_sixteenth_root n) hrootPos.le

/-- Four sixteenth-root factors and one fourth-root factor multiply to the
square root of the main logarithm. -/
theorem roots_mul_eq_sqrt (n : Nat) :
    ((logScale n) ^ (1 / 16 : ℝ)) ^ 4 * rootScale n =
      Real.sqrt (logScale n) := by
  have hΛ : 0 ≤ logScale n := by linarith [logScale_ge_two n]
  have hfour : ((logScale n) ^ (1 / 16 : ℝ)) ^ 4 = rootScale n := by
    dsimp [rootScale]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ]
    norm_num
  rw [hfour]
  dsimp [rootScale]
  rw [← pow_two, ← Real.rpow_natCast, ← Real.rpow_mul hΛ,
    Real.sqrt_eq_rpow]
  norm_num

/-- At the explicit schedule, the full SAT query exponent is bounded by a
constant times `n / (lg(n+4))^(1/4)`. -/
theorem queryExponent_le (C n : Nat) (hn : 1 ≤ n) :
    RateTradeoff.queryExponent C n (bitWidth n) ≤
      (816 * 65 ^ 3 * (C : ℝ)) * (n : ℝ) / rootScale n := by
  let t : ℝ := (logScale n) ^ (1 / 16 : ℝ)
  let s : ℝ := Real.sqrt (logScale n)
  let ℓ : ℝ := bitWidth n
  have ht : 0 < t := by
    dsimp [t]
    exact Real.rpow_pos_of_pos (by linarith [logScale_ge_two n]) _
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr (by linarith [logScale_ge_two n])
  have hx : 0 < rootScale n := by linarith [rootScale_ge_one n]
  have hmax : max (2 * bitWidth n) 2 = 2 * bitWidth n := by
    exact max_eq_left (by have := bitWidth_pos n; omega)
  have hmul : 1 ≤ n * bitWidth n := Nat.mul_pos hn (bitWidth_pos n)
  have hvars : (((2 * n * bitWidth n : Nat) : ℝ) + 4) ≤
      6 * (n : ℝ) * ℓ := by
    have hmulR : (1 : ℝ) ≤ (n : ℝ) * ℓ := by
      dsimp [ℓ]
      exact_mod_cast hmul
    dsimp [ℓ]
    push_cast
    nlinarith
  have hrate : SatK.rN 1 (1 / 2) (2 * n * bitWidth n) ≤ 34 * t / s :=
    query_rate_le n
  have hvars' : 2 * (n : ℝ) * ℓ + 4 ≤ 6 * (n : ℝ) * ℓ := by
    simpa only [ℓ, Nat.cast_mul, Nat.cast_ofNat] using hvars
  have hℓ3 : ℓ ^ 3 ≤ (65 * t) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    exact bitWidth_le_sixteenth_root n
  have hfirst : RateTradeoff.queryExponent C n (bitWidth n) ≤
      (C : ℝ) * (2 * ℓ) ^ 2 * (6 * (n : ℝ) * ℓ) * (34 * t / s) := by
    unfold RateTradeoff.queryExponent
    rw [hmax]
    push_cast
    change (C : ℝ) * (2 * ℓ) ^ 2 * (2 * (n : ℝ) * ℓ + 4) *
      SatK.rN 1 (1 / 2) (2 * n * bitWidth n) ≤ _
    have hcoef : 0 ≤ (C : ℝ) * (2 * ℓ) ^ 2 := by positivity
    calc
      (C : ℝ) * (2 * ℓ) ^ 2 *
          (2 * (n : ℝ) * ℓ + 4) *
            SatK.rN 1 (1 / 2) (2 * n * bitWidth n) ≤
        (C : ℝ) * (2 * ℓ) ^ 2 * (6 * (n : ℝ) * ℓ) *
            SatK.rN 1 (1 / 2) (2 * n * bitWidth n) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hvars' hcoef)
            (Wrap.Arith.rate_nonneg _)
      _ ≤ (C : ℝ) * (2 * ℓ) ^ 2 * (6 * (n : ℝ) * ℓ) * (34 * t / s) :=
        mul_le_mul_of_nonneg_left hrate (by positivity)
  calc
    RateTradeoff.queryExponent C n (bitWidth n) ≤
        (C : ℝ) * (2 * ℓ) ^ 2 * (6 * (n : ℝ) * ℓ) * (34 * t / s) := hfirst
    _ = (816 * (C : ℝ) * (n : ℝ)) * (ℓ ^ 3) * (t / s) := by ring
    _ ≤ (816 * (C : ℝ) * (n : ℝ)) * ((65 * t) ^ 3) * (t / s) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hℓ3 (by positivity)
    _ = (816 * 65 ^ 3 * (C : ℝ)) * (n : ℝ) / rootScale n := by
      have hroots := roots_mul_eq_sqrt n
      dsimp [t, s] at hroots ⊢
      rw [← hroots]
      field_simp [ht.ne', hx.ne']
      have ht' : logScale n ^ (1 / 16 : ℝ) ≠ 0 := by
        exact (Real.rpow_pos_of_pos (by linarith [logScale_ge_two n]) _).ne'
      field_simp [ht']

/-- Rounding down loses at most a factor two because the root scale is at
least one. -/
theorem rootScale_le_twice_blockLength (n : Nat) :
    rootScale n ≤ 2 * (blockLength n : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (rootScale n)
  have hpos : 1 ≤ blockLength n := blockLength_pos n
  have hmax : ⌊rootScale n⌋₊ ≤ blockLength n := Nat.le_max_right _ _
  have hcast : (⌊rootScale n⌋₊ : ℝ) ≤ blockLength n := by exact_mod_cast hmax
  have hposR : (1 : ℝ) ≤ blockLength n := by exact_mod_cast hpos
  linarith

/-- The real branch factor is at most a fixed multiple of the inverse root
scale for every market size. -/
theorem branch_div_le (n : Nat) :
    (8 : ℝ) / (blockLength n : ℝ) ≤ 16 / rootScale n := by
  have hD : (0 : ℝ) < blockLength n := by exact_mod_cast blockLength_pos n
  have hx : 0 < rootScale n := by have := rootScale_ge_one n; linarith
  apply (div_le_div_iff₀ hD hx).mpr
  nlinarith [rootScale_le_twice_blockLength n]

/-- The integer-division branch exponent obeys the same inverse fourth-root
rate, up to its two-query constant. -/
theorem branch_exponent_le (n : Nat) :
    (((2 + 8 * n / blockLength n : Nat) : ℝ)) ≤
      2 + 16 * (n : ℝ) / rootScale n := by
  have hquot : (((8 * n) / blockLength n : Nat) : ℝ) ≤
      (8 * (n : ℝ)) / blockLength n := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_div_le (α := ℝ) (m := 8 * n) (n := blockLength n))
  have hscale := mul_le_mul_of_nonneg_right (branch_div_le n)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  calc
    (((2 + 8 * n / blockLength n : Nat) : ℝ)) =
        2 + (((8 * n) / blockLength n : Nat) : ℝ) := by push_cast; ring
    _ ≤ 2 + (8 * (n : ℝ)) / blockLength n := add_le_add_right hquot _
    _ = 2 + ((8 : ℝ) / blockLength n) * n := by ring
    _ ≤ 2 + (16 / rootScale n) * n := add_le_add_right hscale _
    _ = 2 + 16 * (n : ℝ) / rootScale n := by ring

/-- The fixed additive branch cost is also covered by the inverse-root
scale once the market has at least one participant. -/
theorem two_le_inverse_root (n : Nat) (hn : 1 ≤ n) :
    (2 : ℝ) ≤ 16 * (n : ℝ) / rootScale n := by
  have hx : 0 < rootScale n := by linarith [rootScale_ge_one n]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hupper : rootScale n ≤ 8 * (n : ℝ) := by
    linarith [rootScale_le_logScale n, logScale_le_linear n]
  apply (le_div_iff₀ hx).mpr
  nlinarith

/-- The explicit logarithmic schedule bounds the complete exponent, for
every positive market size. -/
theorem exponent_le (C n : Nat) (hn : 1 ≤ n) :
    RateTradeoff.exponent C n (blockLength n) (bitWidth n) ≤
      ((32 + 816 * 65 ^ 3 * C : Nat) : ℝ) * (n : ℝ) / rootScale n := by
  have hbranch := branch_exponent_le n
  have hquery := queryExponent_le C n hn
  have htwo := two_le_inverse_root n hn
  unfold RateTradeoff.exponent
  have hsum : 2 + 16 * (n : ℝ) / rootScale n +
      (816 * 65 ^ 3 * (C : ℝ)) * (n : ℝ) / rootScale n ≤
      ((32 + 816 * 65 ^ 3 * C : Nat) : ℝ) * (n : ℝ) / rootScale n := by
    calc
      2 + 16 * (n : ℝ) / rootScale n +
          (816 * 65 ^ 3 * (C : ℝ)) * (n : ℝ) / rootScale n ≤
        16 * (n : ℝ) / rootScale n + 16 * (n : ℝ) / rootScale n +
          (816 * 65 ^ 3 * (C : ℝ)) * (n : ℝ) / rootScale n := by
            linarith [htwo]
      _ = ((32 + 816 * 65 ^ 3 * C : Nat) : ℝ) * (n : ℝ) / rootScale n := by
        push_cast
        ring
  exact (add_le_add hbranch hquery).trans hsum

/-- A direct quantified form of the fourth-root-logarithm time exponent.
The threshold can be taken to be one. -/
theorem exists_logarithmic_rate (C : Nat) :
    ∃ K N : Nat, ∀ n ≥ N,
      RateTradeoff.exponent C n (blockLength n) (bitWidth n) ≤
        (K : ℝ) * (n : ℝ) /
          (lg ((n : ℝ) + 4)) ^ (1 / 4 : ℝ) := by
  refine ⟨32 + 816 * 65 ^ 3 * C, 1, ?_⟩
  intro n hn
  exact exponent_le C n hn


end StableMatching.LogarithmicRate
