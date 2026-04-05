import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem coe_set_mk {toSubmonoid : Submonoid R} (add_mem zero_mem) :
    (Subsemiring.mk toSubmonoid add_mem zero_mem : Set R) = toSubmonoid := rfl

