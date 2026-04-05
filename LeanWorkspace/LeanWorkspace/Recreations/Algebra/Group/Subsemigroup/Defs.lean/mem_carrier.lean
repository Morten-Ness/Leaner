import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

theorem mem_carrier {s : Subsemigroup M} {x : M} : x ∈ s.carrier ↔ x ∈ s := Iff.rfl

