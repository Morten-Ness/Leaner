import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem eval_pow (n : ℕ) : (p ^ n).eval x = p.eval x ^ n := Polynomial.eval₂_pow _ _ _

