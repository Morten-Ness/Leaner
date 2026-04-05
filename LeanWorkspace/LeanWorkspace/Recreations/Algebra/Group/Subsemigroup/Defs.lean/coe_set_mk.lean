import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

theorem coe_set_mk (s : Set M) (h_mul) : (Subsemigroup.mk s h_mul : Set M) = s := rfl

