import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.inv {M : Type*} [DivisionMonoid M] {f : α → M}
    (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport f⁻¹ := hf.comp inv_one

