import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

variable [InvolutiveStar R] [StarRing A] [StarModule R A]

theorem star_mem_resolventSet_iff {r : R} {a : A} :
    star r ∈ resolventSet R a ↔ r ∈ resolventSet R (star a) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    simpa only [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, star_sub, star_smul,
      star_star, star_one] using IsUnit.star h

