import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable {S : Subsemigroup M}

theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s := rfl

