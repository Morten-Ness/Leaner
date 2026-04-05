import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_update_ne_zero (p : R[X]) (n : ℕ) {a : R} (ha : a ≠ 0) :
    Polynomial.support (p.update n a) = insert n p.support := by classical rw [Polynomial.support_update, if_neg ha]

