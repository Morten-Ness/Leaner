import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)) : h.unit = a := Units.ext rfl

