import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem coe_sInf (S : Set (Submonoid M)) : ((sInf S : Submonoid M) : Set M) = ⋂ s ∈ S, ↑s := rfl

