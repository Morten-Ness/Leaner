import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add_right (c : M) (h : a ≡ b [PMOD p]) : a + c ≡ b + c [PMOD p] := by
  simpa [add_comm] using h.add_left c
