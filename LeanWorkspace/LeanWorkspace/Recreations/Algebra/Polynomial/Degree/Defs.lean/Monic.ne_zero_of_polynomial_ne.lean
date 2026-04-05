import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem Monic.ne_zero_of_polynomial_ne {r} (hp : Polynomial.Monic p) (hne : q ≠ r) : p ≠ 0 := haveI := Nontrivial.of_polynomial_ne hne
  hp.ne_zero

