import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem unit_pow (h : IsUnit a) (n : ℕ) : (h.pow n).unit = h.unit ^ n := Units.ext rfl

