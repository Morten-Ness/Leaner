import Mathlib

variable {A R : Type*} [AddGroup A] [Fintype A] [CommSemiring R] [IsDomain R]
  {ψ : AddChar A R}

variable [CharZero R]

theorem sum_eq_zero_iff_ne_zero : ∑ x, ψ x = 0 ↔ ψ ≠ 0 := by
  classical
  rw [AddChar.sum_eq_ite, Ne.ite_eq_right_iff]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

