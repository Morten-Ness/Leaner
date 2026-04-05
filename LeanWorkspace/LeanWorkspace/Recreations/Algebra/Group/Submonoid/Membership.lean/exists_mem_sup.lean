import Mathlib

variable {M A B : Type*}

variable {N : Type*} [CommMonoid N]

variable {P : N → Prop}

theorem exists_mem_sup {s t : Submonoid N} :
    (∃ x ∈ s ⊔ t, P x) ↔ (∃ x₁ ∈ s, ∃ x₂ ∈ t, P (x₁ * x₂)) := by
  simp [Submonoid.mem_sup]

