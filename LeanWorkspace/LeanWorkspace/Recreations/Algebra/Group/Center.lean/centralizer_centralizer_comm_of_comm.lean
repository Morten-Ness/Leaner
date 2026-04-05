import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem centralizer_centralizer_comm_of_comm (h_comm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ S.centralizer.centralizer, ∀ y ∈ S.centralizer.centralizer, x * y = y * x := fun _ h₁ _ h₂ ↦ h₂ _ fun _ h₃ ↦ h₁ _ fun _ h₄ ↦ h_comm _ h₄ _ h₃

