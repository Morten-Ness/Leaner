import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [CommSemiring S] (f : R →+* S) (x : S)

theorem eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.eval₂ f x := Polynomial.eval₂_mul_noncomm _ _ fun _k => Commute.all _ _

