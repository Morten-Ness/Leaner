import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

theorem mk_le_mk {s t : Subsemigroup M} (h_one) (h_one') : Submonoid.mk s h_one ≤ Submonoid.mk t h_one' ↔ s ≤ t := Iff.rfl

