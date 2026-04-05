import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable {S : Submonoid M}

theorem mem_bot {x : M} : x ∈ (⊥ : Submonoid M) ↔ x = 1 := Set.mem_singleton_iff

