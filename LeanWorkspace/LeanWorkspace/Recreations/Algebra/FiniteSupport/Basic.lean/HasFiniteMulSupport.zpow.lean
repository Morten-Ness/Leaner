import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.zpow {M : Type*} [DivisionMonoid M] {f : α → M}
    (hf : HasFiniteMulSupport f) (n : ℤ) :
    HasFiniteMulSupport (f ^ n) := hf.comp (one_zpow n)

