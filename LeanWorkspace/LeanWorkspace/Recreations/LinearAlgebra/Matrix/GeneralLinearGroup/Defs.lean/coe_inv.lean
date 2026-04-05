import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

variable (A B : GL n R)

theorem coe_inv : ↑A⁻¹ = (↑A : Matrix n n R)⁻¹ := letI := A.invertible
  invOf_eq_nonsing_inv (↑A : Matrix n n R)

