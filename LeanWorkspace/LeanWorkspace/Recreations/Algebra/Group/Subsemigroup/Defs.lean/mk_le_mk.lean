import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

theorem mk_le_mk {s t : Set M} (h_mul) (h_mul') : Subsemigroup.mk s h_mul ≤ Subsemigroup.mk t h_mul' ↔ s ⊆ t := Iff.rfl

