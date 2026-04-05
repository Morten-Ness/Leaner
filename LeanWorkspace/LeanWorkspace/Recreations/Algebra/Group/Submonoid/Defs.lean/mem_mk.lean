import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

theorem mem_mk {s : Subsemigroup M} {x : M} (h_one) : x ∈ Submonoid.mk s h_one ↔ x ∈ s := Iff.rfl

