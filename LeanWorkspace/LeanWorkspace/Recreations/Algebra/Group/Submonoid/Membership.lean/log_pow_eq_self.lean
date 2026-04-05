import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem log_pow_eq_self [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m)
    (m : ℕ) : Submonoid.log (Submonoid.pow n m) = m := Submonoid.pow_right_injective_iff_pow_injective.mp h <| Submonoid.pow_log_eq_self _

