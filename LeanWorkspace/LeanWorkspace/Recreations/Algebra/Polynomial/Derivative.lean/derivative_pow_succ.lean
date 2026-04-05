import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem derivative_pow_succ (p : R[X]) (n : ℕ) :
    Polynomial.derivative (p ^ (n + 1)) = Polynomial.C (n + 1 : R) * p ^ n * Polynomial.derivative p := Nat.recOn n (by simp) fun n ih => by
    rw [pow_succ, Polynomial.derivative_mul, ih, Nat.add_one, mul_right_comm, C_add,
      add_mul, add_mul, pow_succ, ← mul_assoc, C_1, one_mul]; simp [add_mul]

