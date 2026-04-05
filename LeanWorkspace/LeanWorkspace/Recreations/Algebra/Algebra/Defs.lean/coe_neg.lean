import Mathlib

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem coe_neg (x : R) : (↑(-x : R) : A) = -↑x := map_neg (algebraMap R A) x

