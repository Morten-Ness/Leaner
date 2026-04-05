import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem unit_spec (h : IsUnit a) : ↑h.unit = a := rfl

