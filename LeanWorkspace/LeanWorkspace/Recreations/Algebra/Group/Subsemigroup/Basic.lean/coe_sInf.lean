import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem coe_sInf (S : Set (Subsemigroup M)) : ((sInf S : Subsemigroup M) : Set M) = ⋂ s ∈ S, ↑s := rfl

