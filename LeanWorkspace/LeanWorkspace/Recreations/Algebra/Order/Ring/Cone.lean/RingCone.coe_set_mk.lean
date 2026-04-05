import Mathlib

theorem RingCone.coe_set_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
    (eq_zero_of_mem_of_neg_mem) :
    (mk toSubsemiring eq_zero_of_mem_of_neg_mem : Set R) = toSubsemiring := rfl

