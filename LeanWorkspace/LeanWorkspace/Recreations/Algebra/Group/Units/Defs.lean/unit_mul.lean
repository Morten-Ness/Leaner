import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem unit_mul (ha : IsUnit a) (hb : IsUnit b) : (ha.mul hb).unit = ha.unit * hb.unit := Units.ext rfl

