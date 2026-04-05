import Mathlib

open scoped Polynomial

variable (M : Type*) [Monoid M]

variable {P : Type*} [CommSemiring P] [MulSemiringAction M P]

variable {Q : Type*} [CommSemiring Q] [MulSemiringAction M Q]

theorem coe_polynomial (g : P →+*[M] Q) : (g.polynomial : P[X] → Q[X]) = map g := rfl

