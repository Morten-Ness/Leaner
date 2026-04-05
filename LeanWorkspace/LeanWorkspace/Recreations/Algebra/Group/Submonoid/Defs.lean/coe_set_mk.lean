import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

theorem coe_set_mk {s : Subsemigroup M} (h_one) : (Submonoid.mk s h_one : Set M) = s := rfl

