import Mathlib

variable {M : Type*} [Monoid M]

theorem mem_units_of_val_mem_inv_val_mem (S : Submonoid M) {x : Mˣ} (h₁ : (x : M) ∈ S)
    (h₂ : ((x⁻¹ : Mˣ) : M) ∈ S) : x ∈ S.units := ⟨h₁, h₂⟩

