import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable {S : Submonoid M}

theorem coe_bot : ((⊥ : Submonoid M) : Set M) = {1} := rfl

