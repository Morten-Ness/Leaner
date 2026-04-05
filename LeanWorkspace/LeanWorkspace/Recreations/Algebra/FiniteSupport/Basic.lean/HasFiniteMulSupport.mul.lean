import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.mul {M : Type*} [MulOneClass M] {f g : α → M}
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport (f * g) := (hf.union hg).subset <| mulSupport_mul ..

