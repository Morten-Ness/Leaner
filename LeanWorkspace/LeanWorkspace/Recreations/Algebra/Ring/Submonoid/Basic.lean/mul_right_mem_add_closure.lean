import Mathlib

variable {M R : Type*} [NonUnitalNonAssocSemiring R] [SetLike M R] [MulMemClass M R] {S : M}
  {a b : R}

theorem mul_right_mem_add_closure (ha : a ∈ closure (S : Set R)) (hb : b ∈ S) :
    a * b ∈ closure (S : Set R) := by
  induction ha using closure_induction with
  | mem r hr => exact mem_closure.mpr fun y hy => hy (mul_mem hr hb)
  | zero => simp only [zero_mul, zero_mem _]
  | add r s _ _ hr hs => simpa only [add_mul] using add_mem hr hs

