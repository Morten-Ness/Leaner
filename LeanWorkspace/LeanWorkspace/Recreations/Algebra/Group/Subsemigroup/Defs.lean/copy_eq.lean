import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable {S : Subsemigroup M}

theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S := SetLike.coe_injective hs

