import Mathlib

variable {M : Type*} [Monoid M]

theorem val_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) : (x : M) ∈ S := h.1

