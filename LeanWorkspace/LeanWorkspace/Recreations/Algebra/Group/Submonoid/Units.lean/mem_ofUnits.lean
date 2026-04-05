import Mathlib

variable {M : Type*} [Monoid M]

theorem mem_ofUnits (S : Subgroup Mˣ) {x : M} {y : Mˣ} (h₁ : y ∈ S) (h₂ : y = x) : x ∈ S.ofUnits := ⟨_, h₁, h₂⟩

