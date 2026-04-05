import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem root_mul_left_of_isRoot (p : R[X]) {q : R[X]} : Polynomial.IsRoot q a → Polynomial.IsRoot (p * q) a := fun H => by
  rw [Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.IsRoot.def.1 H, mul_zero]

