import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable {S : Submonoid M}

theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s := rfl

