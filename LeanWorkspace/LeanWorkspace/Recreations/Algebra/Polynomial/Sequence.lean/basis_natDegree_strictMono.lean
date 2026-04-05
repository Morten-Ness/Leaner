import Mathlib

open scoped Function

variable (R : Type*)

variable [Ring R] (S : Sequence R)

variable [IsDomain R]

variable (hCoeff : ∀ i, IsUnit (S i).leadingCoeff)

theorem basis_natDegree_strictMono : StrictMono <| natDegree ∘ (S.basis hCoeff) := fun _ _ ↦ by simp

