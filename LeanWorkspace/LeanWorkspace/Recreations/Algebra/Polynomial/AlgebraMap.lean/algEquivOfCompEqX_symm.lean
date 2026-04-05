import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem algEquivOfCompEqX_symm (p q : R[X]) (hpq : p.comp q = Polynomial.X) (hqp : q.comp p = Polynomial.X) :
    (Polynomial.algEquivOfCompEqX p q hpq hqp).symm = Polynomial.algEquivOfCompEqX q p hqp hpq := rfl

