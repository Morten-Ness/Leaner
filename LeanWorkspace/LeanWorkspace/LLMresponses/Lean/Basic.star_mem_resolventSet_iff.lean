FAIL
import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

variable [InvolutiveStar R] [StarRing A] [StarModule R A]

theorem star_mem_resolventSet_iff {r : R} {a : A} :
    star r ∈ resolventSet R a ↔ r ∈ resolventSet R (star a) := by
  change IsUnit ((algebraMap R A) (star r) - a) ↔ IsUnit ((algebraMap R A) r - star a)
  rw [← isUnit_star]
  simpa [star_sub] using
    congrArg star (show ((algebraMap R A) (star r) - a) = ((algebraMap R A) (star r) - a) by rfl)
