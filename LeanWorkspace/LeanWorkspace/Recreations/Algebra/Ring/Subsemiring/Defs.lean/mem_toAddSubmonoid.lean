import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable (s : Subsemiring R)

theorem mem_toAddSubmonoid {s : Subsemiring R} {x : R} : x ∈ s.toAddSubmonoid ↔ x ∈ s := Iff.rfl

