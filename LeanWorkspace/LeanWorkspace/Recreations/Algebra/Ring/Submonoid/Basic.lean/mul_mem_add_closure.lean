import Mathlib

variable {M R : Type*} [NonUnitalNonAssocSemiring R] [SetLike M R] [MulMemClass M R] {S : M}
  {a b : R}

theorem mul_mem_add_closure (ha : a ∈ closure (S : Set R))
    (hb : b ∈ closure (S : Set R)) : a * b ∈ closure (S : Set R) := by
  induction hb using closure_induction with
  | mem r hr => exact MulMemClass.mul_right_mem_add_closure ha hr
  | zero => simp only [mul_zero, zero_mem _]
  | add r s _ _ hr hs => simpa only [mul_add] using add_mem hr hs

