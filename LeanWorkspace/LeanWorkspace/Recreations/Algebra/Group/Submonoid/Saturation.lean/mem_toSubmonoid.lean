import Mathlib

variable {M : Type*} [MulOneClass M]

theorem mem_toSubmonoid {s : SaturatedSubmonoid M} {x : M} : x ∈ s.toSubmonoid ↔ x ∈ s := Iff.rfl

