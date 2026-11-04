import ToTuring.Poly.Basic

/-! Encoded output sizes follow from the actual machine certificates and run bounds. -/

namespace StableMatching.MachineOutputSize

open Groundwork

theorem exists_halt {A B : Type} {M : Stepped A B} {S t : Nat} {b : B} {s : M.σ}
    (h : M.Reaches S b s t) : ∃ final : M.σ, M.out final = some b ∧ size final ≤ S := by
  induction h with
  | halt ho hs => exact ⟨_, ho, hs⟩
  | step _ _ _ ih => exact ih

theorem output_length_bound {A B : Type} [Enc A] [Enc B]
    (M : Stepped A B) [IsPolyT M] :
    ∃ q : Nat → Nat, PB q ∧ Monotone q ∧ ∀ (a : A) (t S : Nat) (b : B),
      M.Runs a t S b → len b ≤ q S := by
  obtain ⟨q, hq, hm, hlen⟩ := PolyT.len_bound (IsPolyT.out (M := M))
  refine ⟨fun S => q (7 * S), hq.comp ((PB.const 7).mul PB.id'),
    fun _ _ h => hm (by omega), ?_⟩
  intro a t S b hrun
  obtain ⟨final, ho, hs⟩ := exists_halt hrun
  have hc := Carried.le final
  have hword : len final ≤ 7 * S := by omega
  have hf := hlen final
  rw [ho, len_some] at hf
  exact (by omega : len b ≤ q (len final)).trans (hm hword)

theorem after_length_bound {A B C : Type} [Enc A] [Enc B] [Enc C]
    (M : Stepped A B) [IsPolyT M] (f : A × B → C) (hf : PolyT f) :
    ∃ q : Nat → Nat, PB q ∧ Monotone q ∧ ∀ (a : A) (t S : Nat) (b : B),
      M.Runs a t S b → len (f (a, b)) ≤ q (len a + S) := by
  obtain ⟨r, hr, hrm, hout⟩ := output_length_bound M
  obtain ⟨q, hq, hqm, hlen⟩ := PolyT.len_bound hf
  let p : Nat → Nat := fun n => q (n + r n + 2)
  have hp : PB p := hq.comp ((PB.id'.add hr).add (PB.const 2))
  have hpm : Monotone p := by
    intro x y hxy
    exact hqm (by have := hrm hxy; omega)
  refine ⟨p, hp, hpm, ?_⟩
  intro a t S b hrun
  have hb := hout a t S b hrun
  have hmono := hrm (by omega : S ≤ len a + S)
  have hi : len (a, b) ≤ len a + S + r (len a + S) + 2 := by
    rw [len_pair]
    omega
  exact (hlen (a, b)).trans (hqm hi)

end StableMatching.MachineOutputSize
