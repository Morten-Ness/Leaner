import Mathlib

variable {M : Type*} [Monoid M]

theorem unit_eq_unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
    (h₂ : x ∈ S.ofUnits) : h₁.unit = S.unit_of_mem_ofUnits h₂ := Units.ext rfl

