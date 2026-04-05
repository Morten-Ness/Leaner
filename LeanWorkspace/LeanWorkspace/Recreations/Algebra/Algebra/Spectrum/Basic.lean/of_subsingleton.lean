import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem of_subsingleton [Subsingleton A] (a : A) : spectrum R a = ∅ := by
  rw [spectrum, spectrum.resolventSet_of_subsingleton, Set.compl_univ]

