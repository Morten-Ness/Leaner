import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable {S : Submonoid M}

theorem coe_top : ((⊤ : Submonoid M) : Set M) = Set.univ := rfl

