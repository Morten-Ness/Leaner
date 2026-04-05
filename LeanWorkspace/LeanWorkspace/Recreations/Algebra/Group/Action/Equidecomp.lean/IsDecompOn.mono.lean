import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [SMul G X]

theorem IsDecompOn.mono {f f' : X → X} {A A' : Set X} {S : Finset G} (h : Equidecomp.IsDecompOn f A S)
    (hA' : A' ⊆ A) (hf' : EqOn f f' A') : Equidecomp.IsDecompOn f' A' S := by
  intro a ha
  rw [← hf' ha]
  exact h a (hA' ha)

