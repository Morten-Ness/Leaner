import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

theorem mem_toSubsemigroup {s : Submonoid M} {x : M} : x ∈ s.toSubsemigroup ↔ x ∈ s := Iff.rfl

