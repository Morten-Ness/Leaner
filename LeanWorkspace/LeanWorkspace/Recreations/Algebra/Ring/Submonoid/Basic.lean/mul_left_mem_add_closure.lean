import Mathlib

variable {M R : Type*} [NonUnitalNonAssocSemiring R] [SetLike M R] [MulMemClass M R] {S : M}
  {a b : R}

theorem mul_left_mem_add_closure (ha : a ∈ S) (hb : b ∈ closure (S : Set R)) :
    a * b ∈ closure (S : Set R) := MulMemClass.mul_mem_add_closure (mem_closure.mpr fun _sT hT => hT ha) hb

