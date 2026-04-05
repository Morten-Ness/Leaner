import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_update_ne (p : R[X]) {n : ℕ} (a : R) {i : ℕ} (h : i ≠ n) :
    (p.update n a).coeff i = p.coeff i := by rw [Polynomial.coeff_update_apply p, if_neg h]

