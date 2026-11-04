import StableMatching.RawBranching
import StableMatching.ExecutableSchedule

/-! Actual polynomial-time certificates for the executable uniform schedule.
The search implementation of square root is used only on unary-bounded numbers.
Its equality with `Nat.sqrt` is proved, rather than assuming its running time. -/

namespace StableMatching.ScheduleComplexity

open Groundwork

def sqrtSearch (n : Nat) : Nat :=
  (((List.range (n + 1)).filter (fun k => decide (k * k ≤ n))).argmax id).getD 0

theorem sqrtSearch_eq (n : Nat) : sqrtSearch n = Nat.sqrt n := by
  let xs := (List.range (n + 1)).filter (fun k => decide (k * k ≤ n))
  have hmem : Nat.sqrt n ∈ xs := List.mem_filter.mpr
    ⟨List.mem_range.mpr (by have := Nat.sqrt_le_self n; omega), by simp [Nat.sqrt_le n]⟩
  cases hp : xs.argmax id with
  | none =>
    have he := List.argmax_eq_none.mp hp
    rw [he] at hmem
    cases hmem
  | some k =>
    have harg : k ∈ xs.argmax id := by simpa only [Option.mem_def] using hp
    have hk := List.argmax_mem harg
    have hkn : k * k ≤ n := of_decide_eq_true (List.mem_filter.mp hk).2
    have hlow : Nat.sqrt n ≤ k := List.le_of_mem_argmax hmem harg
    have heq : k = Nat.sqrt n := le_antisymm (Nat.le_sqrt.mpr hkn) hlow
    unfold sqrtSearch
    change (xs.argmax id).getD 0 = _
    rw [hp, Option.getD_some, heq]

theorem sqrt_polyT {A : Type} [Enc A] {n : A → Nat} (hn : Unary n) :
    PolyT (fun a => Nat.sqrt (n a)) := by
  have hnp := hn.poly
  have hr := PolyT.range (hn.add (Unary.const 1))
  have hf : PolyT (fun a => (List.range (n a + 1)).filter (fun k => decide (k * k ≤ n a))) := by
    fun_prop
  have hm := RawBranching.argmax_polyT (f := fun (_ : A) k => k) hf (by fun_prop)
  have hs : PolyT (fun a => sqrtSearch (n a)) := by
    unfold sqrtSearch
    fun_prop
  exact hs.congr (fun a => sqrtSearch_eq (n a))

theorem sqrt_unary {A : Type} [Enc A] {n : A → Nat} (hn : Unary n) :
    Unary (fun a => Nat.sqrt (n a)) :=
  Unary.of_le hn (sqrt_polyT hn) (fun a => Nat.sqrt_le_self (n a))

theorem clog_two_succ_eq_size (n : Nat) : Nat.clog 2 (n + 1) = Nat.size n := by
  apply le_antisymm
  · exact Nat.clog_le_of_le_pow (Nat.succ_le_of_lt (Nat.lt_size_self n))
  · exact Nat.size_le.mpr (Nat.lt_of_succ_le (Nat.le_pow_clog Nat.one_lt_two (n + 1)))

theorem blockLength_le (n : Nat) : ExecutableSchedule.blockLength n ≤ n + 4 := by
  have hs1 := Nat.sqrt_le_self (Nat.log2 (n + 4))
  have hs2 := Nat.sqrt_le_self (Nat.sqrt (Nat.log2 (n + 4)))
  have hl := Nat.log2_le_self (n + 4)
  simp only [ExecutableSchedule.blockLength, max_le_iff]
  omega

theorem blockLength_polyT {A : Type} [Enc A] {n : A → Nat} (hn : Unary n) :
    PolyT (fun a => ExecutableSchedule.blockLength (n a)) := by
  have hnp := hn.poly
  have hlog : PolyT (fun a => Nat.log2 (n a + 4)) := by fun_prop
  have hlogU : Unary (fun a => Nat.log2 (n a + 4)) :=
    Unary.of_le (hn.add (Unary.const 4)) hlog (fun a => Nat.log2_le_self _)
  have hs := sqrt_polyT (sqrt_unary hlogU)
  unfold ExecutableSchedule.blockLength
  fun_prop

theorem blockLength_unary {A : Type} [Enc A] {n : A → Nat} (hn : Unary n) :
    Unary (fun a => ExecutableSchedule.blockLength (n a)) :=
  Unary.of_le (hn.add (Unary.const 4)) (blockLength_polyT hn) (fun a => blockLength_le _)

theorem bitWidth_polyT {A : Type} [Enc A] {n : A → Nat} (hn : Unary n) :
    PolyT (fun a => ExecutableSchedule.bitWidth (n a)) := by
  have hb := blockLength_polyT hn
  have hs : PolyT (fun a => Nat.size (ExecutableSchedule.blockLength (n a))) := by fun_prop
  exact hs.congr (fun a => (clog_two_succ_eq_size _).symm)

theorem bitWidth_unary {A : Type} [Enc A] {n : A → Nat} (hn : Unary n) :
    Unary (fun a => ExecutableSchedule.bitWidth (n a)) :=
  Unary.of_le ((blockLength_unary hn).add (Unary.const 1)) (bitWidth_polyT hn)
    (fun a => CompactSize.bitWidth_le _)

theorem domainSize_unary {A : Type} [Enc A] {n : A → Nat} (hn : Unary n) :
    Unary (fun a => 2 ^ ExecutableSchedule.bitWidth (n a)) :=
  Unary.of_le ((Unary.const 2).mul ((blockLength_unary hn).add (Unary.const 1)))
    (PolyT.two_pow (bitWidth_unary hn))
    (fun a => CompactSize.bitWidth_pow_le_twice (ExecutableSchedule.blockLength_pos _))

theorem domain_polyT {A : Type} [Enc A] {n : A → Nat} (hn : Unary n) :
    PolyT (fun a => List.range (2 ^ ExecutableSchedule.bitWidth (n a))) :=
  PolyT.range (domainSize_unary hn)

end StableMatching.ScheduleComplexity
