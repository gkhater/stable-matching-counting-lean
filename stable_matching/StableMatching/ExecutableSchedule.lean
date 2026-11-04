import StableMatching.LogarithmicRate
import Mathlib.Data.Nat.Sqrt

/-!
# Executable logarithmic block schedule

Two integer square roots compute the integer fourth root of the binary
logarithm. The resulting block length agrees exactly with the real-log
schedule used in the exponent proof.
-/

namespace StableMatching.ExecutableSchedule

/-- A fully executable block length. -/
def blockLength (n : Nat) : Nat :=
  max 1 (Nat.sqrt (Nat.sqrt (Nat.log2 (n + 4))))

/-- A fully executable bit width for the chosen block length. -/
def bitWidth (n : Nat) : Nat := CompactSize.bitWidth (blockLength n)

theorem blockLength_pos (n : Nat) : 0 < blockLength n := by
  simp [blockLength]

theorem bitWidth_pos (n : Nat) : 0 < bitWidth n :=
  CompactSize.bitWidth_pos (blockLength_pos n)

theorem bitWidth_capacity (n : Nat) : blockLength n + 1 ≤ 2 ^ bitWidth n :=
  CompactSize.bitWidth_capacity (blockLength n)

/-- Two integer square roots characterize the largest integer whose fourth
power does not exceed the input. -/
theorem le_sqrt_sqrt_iff (d q : Nat) :
    d ≤ Nat.sqrt (Nat.sqrt q) ↔ d ^ 4 ≤ q := by
  calc
    d ≤ Nat.sqrt (Nat.sqrt q) ↔ d ^ 2 ≤ Nat.sqrt q := Nat.le_sqrt'
    _ ↔ (d ^ 2) ^ 2 ≤ q := Nat.le_sqrt'
    _ ↔ d ^ 4 ≤ q := by ring

/-- Mathlib's real logarithm and natural binary logarithm have matching
integer floors. -/
theorem natFloor_logScale (n : Nat) :
    ⌊LogarithmicRate.logScale n⌋₊ = Nat.log2 (n + 4) := by
  rw [Nat.log2_eq_log_two]
  simpa only [LogarithmicRate.logScale, MainTheoremForms.lg, Nat.cast_add,
    Nat.cast_ofNat] using (Real.natFloor_logb_natCast 2 (n + 4))

theorem rootScale_pow_four (n : Nat) :
    (LogarithmicRate.rootScale n) ^ 4 = LogarithmicRate.logScale n := by
  have hΛ : 0 ≤ LogarithmicRate.logScale n := by
    linarith [LogarithmicRate.logScale_ge_two n]
  dsimp [LogarithmicRate.rootScale]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ]
  norm_num

/-- The integer implementation is exactly the analytical rounded fourth
root, for every input size. -/
theorem fourthRoot_eq_floor (n : Nat) :
    Nat.sqrt (Nat.sqrt (Nat.log2 (n + 4))) =
      ⌊LogarithmicRate.rootScale n⌋₊ := by
  let q : Nat := Nat.log2 (n + 4)
  let d : Nat := Nat.sqrt (Nat.sqrt q)
  have hΛ : 0 ≤ LogarithmicRate.logScale n := by
    linarith [LogarithmicRate.logScale_ge_two n]
  have hx : 0 ≤ LogarithmicRate.rootScale n := by
    linarith [LogarithmicRate.rootScale_ge_one n]
  have hfloor : ⌊LogarithmicRate.logScale n⌋₊ = q := natFloor_logScale n
  have hpow := rootScale_pow_four n
  apply le_antisymm
  · apply (Nat.le_floor_iff hx).mpr
    have h4 : d ^ 4 ≤ q := (le_sqrt_sqrt_iff d q).mp le_rfl
    have h4R : ((d : ℝ) ^ 4) ≤ LogarithmicRate.logScale n := by
      have hcast : ((d ^ 4 : Nat) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h4
      have hfloorR : (q : ℝ) ≤ LogarithmicRate.logScale n := by
        rw [← hfloor]
        exact Nat.floor_le hΛ
      simpa only [Nat.cast_pow] using hcast.trans hfloorR
    have hbase := (pow_le_pow_iff_left₀ (Nat.cast_nonneg d) hx
      (by norm_num : (4 : Nat) ≠ 0)).mp (by simpa only [hpow] using h4R)
    exact hbase
  · apply (le_sqrt_sqrt_iff _ q).mpr
    have hbase : (⌊LogarithmicRate.rootScale n⌋₊ : ℝ) ≤
        LogarithmicRate.rootScale n := Nat.floor_le hx
    have h4R : ((⌊LogarithmicRate.rootScale n⌋₊ ^ 4 : Nat) : ℝ) ≤
        LogarithmicRate.logScale n := by
      have h4' := (pow_le_pow_iff_left₀
        (Nat.cast_nonneg ⌊LogarithmicRate.rootScale n⌋₊) hx
        (by norm_num : (4 : Nat) ≠ 0)).mpr hbase
      simpa only [Nat.cast_pow, hpow] using h4'
    have h4Nat : ⌊LogarithmicRate.rootScale n⌋₊ ^ 4 ≤ q := by
      rw [← hfloor]
      exact (Nat.le_floor_iff hΛ).mpr h4R
    exact h4Nat

theorem blockLength_eq (n : Nat) :
    blockLength n = LogarithmicRate.blockLength n := by
  simp only [blockLength, LogarithmicRate.blockLength, fourthRoot_eq_floor]

theorem bitWidth_eq (n : Nat) :
    bitWidth n = LogarithmicRate.bitWidth n := by
  simp only [bitWidth, LogarithmicRate.bitWidth, blockLength_eq]

end StableMatching.ExecutableSchedule
