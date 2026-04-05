import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

theorem mem_carrier {s : Submonoid M} {x : M} : x ∈ s.carrier ↔ x ∈ s := Iff.rfl

