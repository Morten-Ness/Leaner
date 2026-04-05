import Mathlib

variable {R : Type*} [Ring R]

theorem taylor_injective (r : R) : Function.Injective (Polynomial.taylor r) := (injective_iff_map_eq_zero' _).2 (Polynomial.taylor_eq_zero r)

