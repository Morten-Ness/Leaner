import Mathlib

open scoped Function

variable (R : Type*)

variable [Ring R] (S : Sequence R)

variable [IsDomain R]

variable (hCoeff : ∀ i, IsUnit (S i).leadingCoeff)

theorem basis_degree_strictMono : StrictMono <| degree ∘ (S.basis hCoeff) := fun _ _ ↦ by simp

