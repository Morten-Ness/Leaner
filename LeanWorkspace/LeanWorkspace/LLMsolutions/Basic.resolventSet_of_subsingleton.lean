FAIL
import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem resolventSet_of_subsingleton [Subsingleton A] (a : A) : resolventSet R a = Set.univ := by
  ext r
  simp [resolventSet]
  have h0 : (0 : A) = 1 := Subsingleton.elim _ _
  refine ⟨?_, ?_⟩
  · intro _
    trivial
  · intro _
    refine ⟨0, 0, ?_, ?_⟩ <;> simpa [h0]
