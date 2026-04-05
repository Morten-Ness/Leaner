import Mathlib

open scoped Algebra

variable (R : Type*) [Ring R]

theorem algebraMap_int_eq : algebraMap ℤ R = Int.castRingHom R := rfl

