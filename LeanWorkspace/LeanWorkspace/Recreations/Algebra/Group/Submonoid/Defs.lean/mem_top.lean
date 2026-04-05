import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable {S : Submonoid M}

theorem mem_top (x : M) : x ∈ (⊤ : Submonoid M) := Set.mem_univ x

