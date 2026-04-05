import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable {S : Subsemigroup M}

theorem coe_bot : ((⊥ : Subsemigroup M) : Set M) = ∅ := rfl

