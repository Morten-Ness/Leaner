import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_mul {f g : R[X]} : Polynomial.derivative (f * g) = Polynomial.derivative f * g + f * Polynomial.derivative g := by
  induction f using Polynomial.induction_on' with
  | add => simp only [add_mul, map_add, add_assoc, add_left_comm, *]
  | monomial m a => ?_
  induction g using Polynomial.induction_on' with
  | add => simp only [mul_add, map_add, add_assoc, add_left_comm, *]
  | monomial n b => ?_
  simp only [monomial_mul_monomial, Polynomial.derivative_monomial]
  simp only [mul_assoc, (Nat.cast_commute _ _).eq, Nat.cast_add, mul_add, map_add]
  cases m with
  | zero => simp only [zero_add, Nat.cast_zero, mul_zero, map_zero]
  | succ m =>
  cases n with
  | zero => simp only [add_zero, Nat.cast_zero, mul_zero, map_zero]
  | succ n => grind

