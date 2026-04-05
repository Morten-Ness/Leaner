import Mathlib

variable {M : Type*} [Monoid M]

theorem unit_of_mem_ofUnits_spec_val_eq_of_mem (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) :
    S.unit_of_mem_ofUnits h = x := rfl

