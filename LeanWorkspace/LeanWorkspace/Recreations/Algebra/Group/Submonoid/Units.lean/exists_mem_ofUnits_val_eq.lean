import Mathlib

variable {M : Type*} [Monoid M]

theorem exists_mem_ofUnits_val_eq (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) :
    ∃ y ∈ S, y = x := h

