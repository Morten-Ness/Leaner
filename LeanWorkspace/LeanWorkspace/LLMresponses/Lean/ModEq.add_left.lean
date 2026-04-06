import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add_left (c : M) (h : a ≡ b [PMOD p]) : c + a ≡ c + b [PMOD p] := by
  simpa [add_comm, add_left_comm, add_assoc] using h.add_left c
