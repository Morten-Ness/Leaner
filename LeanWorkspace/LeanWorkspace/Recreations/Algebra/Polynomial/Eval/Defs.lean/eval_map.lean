import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem eval_map (x : S) : (p.map f).eval x = p.eval₂ f x := (Polynomial.eval₂_eq_eval_map f).symm

