import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable {S : Submonoid M}

theorem coe_inf (p p' : Submonoid M) : ((p ⊓ p' : Submonoid M) : Set M) = (p : Set M) ∩ p' := rfl

