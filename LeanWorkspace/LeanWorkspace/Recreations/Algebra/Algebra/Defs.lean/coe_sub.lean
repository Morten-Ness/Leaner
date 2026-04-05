import Mathlib

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem coe_sub (a b : R) :
    (↑(a - b : R) : A) = ↑a - ↑b := map_sub (algebraMap R A) a b

