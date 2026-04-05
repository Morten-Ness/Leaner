import Mathlib

open scoped Function

variable (R : Type*)

variable [Semiring R] (S : Sequence R)

theorem natDegree_strictMono : StrictMono <| natDegree ∘ S := fun _ _ ↦ by simp

