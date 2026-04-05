import Mathlib

open scoped Algebra

variable (R : Type*) [Ring R]

theorem algebraMap_comp_intCast (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    algebraMap R A ∘ Int.cast = Int.cast := by
  ext; simp

