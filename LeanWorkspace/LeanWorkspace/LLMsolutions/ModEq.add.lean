import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add (hab : a ≡ b [PMOD p]) (hcd : c ≡ d [PMOD p]) :
    a + c ≡ b + d [PMOD p] := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hab.add hcd
