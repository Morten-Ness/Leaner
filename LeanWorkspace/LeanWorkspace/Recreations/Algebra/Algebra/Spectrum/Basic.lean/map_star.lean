import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

variable [InvolutiveStar R] [StarRing A] [StarModule R A]

theorem map_star (a : A) : σ (star a) = star (σ a) := by
  ext
  simpa only [Set.mem_star, spectrum.mem_iff, not_iff_not] using spectrum.star_mem_resolventSet_iff.symm

