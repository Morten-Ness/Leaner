FAIL
import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem mul_left_iff {a b : M} (ha : IsUnit a) :
    IsUnit (a * b) ↔ IsUnit b := by
  rcases ha with ⟨u, rfl⟩
  constructor
  · intro h
    exact isUnit_of_mul_isUnit_left h
  · intro h
    exact u.isUnit.mul h
