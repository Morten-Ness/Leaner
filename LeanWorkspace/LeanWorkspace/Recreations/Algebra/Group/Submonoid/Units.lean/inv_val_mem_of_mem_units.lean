import Mathlib

variable {M : Type*} [Monoid M]

theorem inv_val_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    ((x⁻¹ : Mˣ) : M) ∈ S := h.2

