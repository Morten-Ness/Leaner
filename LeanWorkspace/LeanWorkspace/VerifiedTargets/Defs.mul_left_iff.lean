import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem mul_left_iff {a b : M} (ha : IsUnit a) :
    IsUnit (a * b) ↔ IsUnit b := show IsUnit (ha.unit * b) ↔ _ by simp [- IsUnit.unit_spec]

grind_pattern mul_left_iff => IsUnit a, IsUnit (a * b)

