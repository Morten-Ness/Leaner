import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [SMul G X]

theorem toPartialEquiv_injective : Function.Injective <| toPartialEquiv (X := X) (G := G) := by
  intro ⟨_, _, _⟩ _ _
  congr

