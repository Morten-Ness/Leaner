FAIL
import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem of_subsingleton [Subsingleton A] (a : A) : spectrum R a = ∅ := by
  ext x
  rw [spectrum, Set.mem_empty_iff_false]
  change ¬ IsUnit (algebraMap R A x - a) ↔ False
  have h : algebraMap R A x - a = 0 := Subsingleton.elim _ _
  rw [h]
  simp
