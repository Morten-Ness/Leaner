FAIL
import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem nsmul_add_modEq (n : ℕ) : n • p + a ≡ a [PMOD p] := by
  simpa [add_assoc, add_left_comm, add_comm] using AddCommMonoid.modEq_add_fac a n p
