import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem coe_evalRingHom (r : R) : (Polynomial.evalRingHom r : R[X] → R) = Polynomial.eval r := rfl

