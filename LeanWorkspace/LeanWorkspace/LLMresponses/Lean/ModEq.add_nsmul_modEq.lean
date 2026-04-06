FAIL
import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add_nsmul_modEq (n : ℕ) : a + n • p ≡ a [PMOD p] := by
  refine ⟨n, ?_⟩
  rw [add_assoc, add_comm (n • p) a]
