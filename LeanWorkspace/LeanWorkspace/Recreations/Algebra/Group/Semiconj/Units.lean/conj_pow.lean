import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem conj_pow (u : Mˣ) (x : M) (n : ℕ) :
    ((↑u : M) * x * (↑u⁻¹ : M)) ^ n = (u : M) * x ^ n * (↑u⁻¹ : M) := eq_divp_iff_mul_eq.2 ((Units.mk_semiconjBy u x).pow_right n).eq.symm

