import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

variable [NoZeroDivisors R]

theorem root_or_root_of_root_mul (h : Polynomial.IsRoot (p * q) a) : Polynomial.IsRoot p a ∨ Polynomial.IsRoot q a := Polynomial.root_mul.1 h

