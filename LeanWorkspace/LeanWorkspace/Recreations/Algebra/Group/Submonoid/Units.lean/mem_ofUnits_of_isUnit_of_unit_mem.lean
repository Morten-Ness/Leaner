import Mathlib

variable {M : Type*} [Monoid M]

theorem mem_ofUnits_of_isUnit_of_unit_mem (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
    (h₂ : h₁.unit ∈ S) : x ∈ S.ofUnits := S.mem_ofUnits h₂ h₁.unit_spec

