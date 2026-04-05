import Mathlib

open scoped Algebra

variable {R : Type*} [Semiring R]

theorem algebraMap_comp_natCast (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    algebraMap R A ∘ Nat.cast = Nat.cast := by
  ext; simp

