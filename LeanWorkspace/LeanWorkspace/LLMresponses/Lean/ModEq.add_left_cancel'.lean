FAIL
import Mathlib

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

theorem add_left_cancel' (c : M) : c + a ≡ c + b [PMOD p] → a ≡ b [PMOD p] := by
  intro h
  simpa [add_assoc, add_left_comm, add_comm] using h.cancel_left c
