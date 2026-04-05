import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_mul_le_of_le {a b : WithBot ℕ} (hp : Polynomial.degree p ≤ a) (hq : Polynomial.degree q ≤ b) :
    Polynomial.degree (p * q) ≤ a + b := by grw [Polynomial.degree_mul_le, hp, hq]

