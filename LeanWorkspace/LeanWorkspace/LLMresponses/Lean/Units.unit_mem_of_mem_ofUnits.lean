import Mathlib

variable {M : Type*} [Monoid M]

theorem unit_mem_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} {h₁ : IsUnit x}
    (h₂ : x ∈ S.ofUnits) : h₁.unit ∈ S := by
  rcases h₂ with ⟨u, hu, rfl⟩
  simpa using hu
