import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_cubic_le : degree (Polynomial.C a * Polynomial.X ^ 3 + Polynomial.C b * Polynomial.X ^ 2 + Polynomial.C c * Polynomial.X + Polynomial.C d) ≤ 3 := by
  simpa only [add_assoc] using
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 3 a)
      (le_trans Polynomial.degree_quadratic_le <| WithBot.coe_le_coe.mpr <| Nat.le_succ 2)

