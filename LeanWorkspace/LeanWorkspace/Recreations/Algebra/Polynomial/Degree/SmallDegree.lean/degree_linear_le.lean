import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_linear_le : degree (Polynomial.C a * Polynomial.X + Polynomial.C b) ≤ 1 := degree_add_le_of_degree_le (degree_C_mul_X_le _) <| le_trans degree_C_le Nat.WithBot.coe_nonneg

