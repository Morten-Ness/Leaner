import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R]

theorem coe_algebraMap_eq_CC : algebraMap R R[X][Y] = CC (R := R) := rfl

