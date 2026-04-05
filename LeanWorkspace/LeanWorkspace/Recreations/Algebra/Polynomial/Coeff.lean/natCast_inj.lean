import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natCast_inj {m n : ℕ} {R : Type*} [Semiring R] [CharZero R] :
    (↑m : R[X]) = ↑n ↔ m = n := by
  constructor
  · intro h
    apply_fun fun p => p.coeff 0 at h
    simpa using h
  · rintro rfl
    rfl

