import Mathlib

variable {M : Type*}

theorem associated_one_of_mul_eq_one [CommMonoid M] {a : M} (b : M) (hab : a * b = 1) : a ~ᵤ 1 := show (Units.mkOfMulEqOne a b hab : M) ~ᵤ 1 from unit_associated_one

