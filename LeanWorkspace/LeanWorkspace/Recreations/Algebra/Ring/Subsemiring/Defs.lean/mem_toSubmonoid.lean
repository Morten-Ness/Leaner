import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem mem_toSubmonoid {s : Subsemiring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s := Iff.rfl

