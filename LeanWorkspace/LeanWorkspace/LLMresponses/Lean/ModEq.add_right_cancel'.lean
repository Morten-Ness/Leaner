import Mathlib

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

theorem add_right_cancel' (c : M) : a + c ≡ b + c [PMOD p] → a ≡ b [PMOD p] := by
  intro h
  rcases h with ⟨m, n, hmn⟩
  refine ⟨m, n, ?_⟩
  exact add_right_cancel <| by simpa [add_assoc, add_left_comm, add_comm] using hmn
