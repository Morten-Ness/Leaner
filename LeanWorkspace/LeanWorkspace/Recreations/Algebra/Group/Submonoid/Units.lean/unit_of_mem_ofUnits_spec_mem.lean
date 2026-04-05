import Mathlib

variable {M : Type*} [Monoid M]

theorem unit_of_mem_ofUnits_spec_mem (S : Subgroup Mˣ) {x : M} {h : x ∈ S.ofUnits} :
    S.unit_of_mem_ofUnits h ∈ S := S.mem_of_mem_val_ofUnits h

