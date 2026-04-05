import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [DivisionMonoid α] {a b c : α}

theorem unit_inv (h : IsUnit a) : IsUnit.inv h.unit = h.unit⁻¹ := Units.ext h.unit.val_inv_eq_inv_val.symm

