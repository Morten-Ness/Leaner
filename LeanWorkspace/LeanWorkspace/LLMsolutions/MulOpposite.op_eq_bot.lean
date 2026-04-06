FAIL
import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_eq_bot {S : Submonoid M} : S.op = ⊥ ↔ S = ⊥ := by
  constructor
  · intro h
    apply le_antisymm
    · intro x hx
      have hx' : MulOpposite.op x ∈ S.op := hx
      rw [h] at hx'
      simpa using hx'
    · exact bot_le
  · intro h
    apply le_antisymm
    · rw [← h]
      exact le_rfl
    · exact bot_le
