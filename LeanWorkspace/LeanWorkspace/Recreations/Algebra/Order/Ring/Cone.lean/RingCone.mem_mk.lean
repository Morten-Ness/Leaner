import Mathlib

theorem RingCone.mem_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
    (eq_zero_of_mem_of_neg_mem) {x : R} :
    x ∈ mk toSubsemiring eq_zero_of_mem_of_neg_mem ↔ x ∈ toSubsemiring := .rfl

