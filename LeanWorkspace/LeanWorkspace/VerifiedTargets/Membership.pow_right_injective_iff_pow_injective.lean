import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem pow_right_injective_iff_pow_injective {n : M} :
    (Function.Injective fun m : ℕ => n ^ m) ↔ Function.Injective (Submonoid.pow n) := Subtype.coe_injective.of_comp_iff (Submonoid.pow n)

