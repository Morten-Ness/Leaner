import Mathlib

open scoped Function

variable (R : Type*)

variable [Semiring R] (S : Sequence R)

theorem degree_strictMono : StrictMono <| degree ∘ S := fun _ _ ↦ by simp

