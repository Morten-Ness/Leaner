import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem unit_one (h : IsUnit (1 : M)) : h.unit = 1 := Units.ext rfl

