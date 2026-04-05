import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R] [NoZeroDivisors R]

theorem derivative_pow_eq_zero {n : ℕ} (chn : (n : R) ≠ 0) {a : R[X]} :
    Polynomial.derivative (a ^ n) = 0 ↔ Polynomial.derivative a = 0 := by
  nontriviality R
  rw [← C_ne_zero, C_eq_natCast] at chn
  simp +contextual [Polynomial.derivative_pow, chn]

