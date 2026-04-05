import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem eval_natCast_map (f : R →+* S) (p : R[X]) (n : ℕ) :
    (p.map f).eval (n : S) = f (p.eval n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [map_natCast f, eval_monomial, map_monomial, f.map_pow, f.map_mul]

