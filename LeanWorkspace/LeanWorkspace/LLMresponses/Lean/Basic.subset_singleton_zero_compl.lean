FAIL
import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem subset_singleton_zero_compl {a : A} (ha : IsUnit a) : spectrum R a ⊆ {0}ᶜ := by
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  subst h
  rw [spectrum.mem_iff] at hx
  simpa using hx ha.map (algebraMap R A)
