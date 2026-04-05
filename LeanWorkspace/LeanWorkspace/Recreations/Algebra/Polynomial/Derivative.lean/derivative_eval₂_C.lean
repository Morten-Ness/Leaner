import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem derivative_eval₂_C (p q : R[X]) :
    Polynomial.derivative (p.eval₂ Polynomial.C q) = p.derivative.eval₂ Polynomial.C q * Polynomial.derivative q := Polynomial.induction_on p (fun r => by rw [eval₂_C, Polynomial.derivative_C, eval₂_zero, zero_mul])
    (fun p₁ p₂ ih₁ ih₂ => by
      rw [eval₂_add, Polynomial.derivative_add, ih₁, ih₂, Polynomial.derivative_add, eval₂_add, add_mul])
    fun n r ih => by
    rw [pow_succ, ← mul_assoc, eval₂_mul, eval₂_X, Polynomial.derivative_mul, ih, @Polynomial.derivative_mul _ _ _ Polynomial.X,
      Polynomial.derivative_X, mul_one, eval₂_add, @eval₂_mul _ _ _ _ Polynomial.X, eval₂_X, add_mul, mul_right_comm]

