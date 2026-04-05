import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem ModEq.trans (hab : a ≡ b [PMOD p]) (hbc : b ≡ c [PMOD p]) :
    a ≡ c [PMOD p] := by
  rw [AddCommGroup.modEq_iff_nsmul] at *
  rcases hab with ⟨m, n, hab⟩
  rcases hbc with ⟨k, l, hbc⟩
  use k + m, n + l
  rw [add_nsmul, add_assoc, hab, add_nsmul, add_assoc, ← hbc, add_left_comm]

