import Mathlib

variable {A R : Type*} [AddGroup A] [Fintype A] [CommSemiring R] [IsDomain R]
  {ψ : AddChar A R}

variable [CharZero R]

theorem sum_ne_zero_iff_eq_zero : ∑ x, ψ x ≠ 0 ↔ ψ = 0 := by
  simpa using AddChar.sum_ne_zero_iff_eq_zero (A := A) (R := R) (ψ := ψ)
