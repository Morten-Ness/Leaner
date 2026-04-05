import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_pow_le_of_le {a : WithBot ℕ} (b : ℕ) (hp : Polynomial.degree p ≤ a) :
    Polynomial.degree (p ^ b) ≤ b * a := by
  induction b with
  | zero => simp [Polynomial.degree_one_le]
  | succ n hn =>
      rw [Nat.cast_succ, add_mul, one_mul, pow_succ]
      exact Polynomial.degree_mul_le_of_le hn hp

