import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [Monoid R] [MulAction R M]

theorem of_mul_eq_one (h : a * b = 1) : IsSMulRegular M b := IsSMulRegular.of_mul (a := a) (by rw [h]; exact IsSMulRegular.one M)

