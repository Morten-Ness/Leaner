import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add (hab : a ≡ b [PMOD p]) (hcd : c ≡ d [PMOD p]) :
    a + c ≡ b + d [PMOD p] := by
  rw [AddCommGroup.modEq_iff_nsmul] at *
  rcases hab with ⟨k, l, hab⟩
  rcases hcd with ⟨m, n, hcd⟩
  use k + m, l + n
  rw [add_nsmul, add_add_add_comm, hab, hcd, add_nsmul, add_add_add_comm]

