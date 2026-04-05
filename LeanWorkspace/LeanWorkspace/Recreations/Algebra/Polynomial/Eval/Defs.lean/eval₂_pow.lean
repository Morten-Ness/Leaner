import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [CommSemiring S] (f : R →+* S) (x : S)

theorem eval₂_pow (n : ℕ) : (p ^ n).eval₂ f x = p.eval₂ f x ^ n := (Polynomial.eval₂RingHom _ _).map_pow _ _

