import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem mul_right_iff {a b : M} (hb : IsUnit b) :
    IsUnit (a * b) ↔ IsUnit a := show IsUnit (a * hb.unit) ↔ _ by simp [- IsUnit.unit_spec]

grind_pattern mul_right_iff => IsUnit b, IsUnit (a * b)

