import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem mem_mk {toSubmonoid : Submonoid R} (add_mem zero_mem) {x : R} :
    x ∈ Subsemiring.mk toSubmonoid add_mem zero_mem ↔ x ∈ toSubmonoid := .rfl

