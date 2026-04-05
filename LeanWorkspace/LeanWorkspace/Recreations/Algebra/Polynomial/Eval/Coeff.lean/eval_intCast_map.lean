import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem eval_intCast_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (p : R[X]) (i : ℤ) :
    (p.map f).eval (i : S) = f (p.eval i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [map_intCast, eval_monomial, map_monomial, map_pow, map_mul]

