import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem pow_right_injective_iff_pow_injective {n : M} :
    (Function.Injective fun m : ℕ => n ^ m) ↔ Function.Injective (Submonoid.pow n) := by
  constructor
  · intro h x y hxy
    apply h
    exact congrArg Subtype.val hxy
  · intro h x y hxy
    apply h
    ext
    exact hxy
