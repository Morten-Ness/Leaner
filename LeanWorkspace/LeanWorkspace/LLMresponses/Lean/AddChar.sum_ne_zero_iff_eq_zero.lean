import Mathlib

variable {A R : Type*} [AddGroup A] [Fintype A] [CommSemiring R] [IsDomain R]
  {ψ : AddChar A R}

variable [CharZero R]

theorem sum_ne_zero_iff_eq_zero : ∑ x, ψ x ≠ 0 ↔ ψ = 0 := by
  rw [ne_eq, AddChar.sum_eq_zero_iff_ne_zero]
  constructor
  · intro h
    exact by_contra h
  · intro h
    simpa [h] using h
