import Mathlib

variable {M : Type*} [Monoid M]

theorem mul_mem_units (S : Submonoid M) {x y : Mˣ} (h₁ : x ∈ S.units) (h₂ : y ∈ S.units) :
    x * y ∈ S.units := mul_mem h₁ h₂

