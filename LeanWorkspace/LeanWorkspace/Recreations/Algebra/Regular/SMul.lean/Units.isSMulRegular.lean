import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable (M) [Monoid R] [MulAction R M]

theorem Units.isSMulRegular (a : Rˣ) : IsSMulRegular M (a : R) := IsSMulRegular.of_mul_eq_one a.inv_val

