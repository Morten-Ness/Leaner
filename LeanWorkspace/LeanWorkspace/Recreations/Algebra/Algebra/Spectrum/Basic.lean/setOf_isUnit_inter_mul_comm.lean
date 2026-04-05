import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem setOf_isUnit_inter_mul_comm (a b : A) :
    {r | IsUnit r} ∩ σ (a * b) = {r | IsUnit r} ∩ σ (b * a) := by
  ext r
  simpa using fun hr : IsUnit r ↦ spectrum.unit_mem_mul_comm (r := hr.unit)

