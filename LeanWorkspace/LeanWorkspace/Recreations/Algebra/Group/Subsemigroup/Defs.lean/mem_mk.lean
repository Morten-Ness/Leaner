import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

theorem mem_mk {s : Set M} {x : M} (h_mul) : x ∈ Subsemigroup.mk s h_mul ↔ x ∈ s := Iff.rfl

