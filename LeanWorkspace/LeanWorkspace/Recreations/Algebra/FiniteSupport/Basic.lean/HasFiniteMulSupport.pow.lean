import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.pow {M : Type*} [Monoid M] {f : α → M} (hf : HasFiniteMulSupport f)
    (n : ℕ) :
    HasFiniteMulSupport (f ^ n) := hf.comp (one_pow n)

