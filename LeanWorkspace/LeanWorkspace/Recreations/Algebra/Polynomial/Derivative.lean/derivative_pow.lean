import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem derivative_pow (p : R[X]) (n : ℕ) :
    Polynomial.derivative (p ^ n) = Polynomial.C (n : R) * p ^ (n - 1) * Polynomial.derivative p := Nat.casesOn n (by simp) fun n ↦
    by rw [Polynomial.derivative_pow_succ p n, Nat.add_one_sub_one, n.cast_succ]

