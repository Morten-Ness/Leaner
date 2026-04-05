import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem log_mul [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m)
    (x y : Submonoid.powers (n : M)) : Submonoid.log (x * y) = Submonoid.log x + Submonoid.log y := map_mul (Submonoid.powLogEquiv h).symm x y

