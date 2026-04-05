import Mathlib

open scoped Ring

variable {R : Type*}

theorem invOf_neg [Monoid R] [HasDistribNeg R] (a : R) [Invertible a] [Invertible (-a)] :
    ⅟(-a) = -⅟a := invOf_eq_right_inv (by simp)

