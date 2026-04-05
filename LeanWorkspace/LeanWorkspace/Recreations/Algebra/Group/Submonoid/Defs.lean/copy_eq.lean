import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable {S : Submonoid M}

theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S := SetLike.coe_injective hs

