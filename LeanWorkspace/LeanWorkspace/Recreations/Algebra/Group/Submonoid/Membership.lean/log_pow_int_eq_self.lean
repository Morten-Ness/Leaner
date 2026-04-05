import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem log_pow_int_eq_self {x : ℤ} (h : 1 < x.natAbs) (m : ℕ) : Submonoid.log (Submonoid.pow x m) = m := (Submonoid.powLogEquiv (Int.pow_right_injective h)).symm_apply_apply _

