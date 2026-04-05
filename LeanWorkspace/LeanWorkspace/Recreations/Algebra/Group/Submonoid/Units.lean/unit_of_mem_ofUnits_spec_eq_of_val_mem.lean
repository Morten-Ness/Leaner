import Mathlib

variable {M : Type*} [Monoid M]

theorem unit_of_mem_ofUnits_spec_eq_of_val_mem (S : Subgroup Mˣ) {x : Mˣ} (h : (x : M) ∈ S.ofUnits) :
    S.unit_of_mem_ofUnits h = x := Units.ext rfl

