import Mathlib

variable {M : Type*}

theorem not_irreducible_zero [MonoidWithZero M] : ¬Irreducible (0 : M)
  | ⟨hn0, h⟩ =>
    have : IsUnit (0 : M) ∨ IsUnit (0 : M) := h (mul_zero 0).symm
    this.elim hn0 hn0

