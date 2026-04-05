import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem monic_X_pow_add_C {n : ℕ} (h : n ≠ 0) : (Polynomial.X ^ n + Polynomial.C a).Monic := Polynomial.monic_X_pow_add <| (lt_of_le_of_lt degree_C_le
    (by simp only [Nat.cast_pos, Nat.pos_iff_ne_zero, ne_eq, h, not_false_eq_true]))

