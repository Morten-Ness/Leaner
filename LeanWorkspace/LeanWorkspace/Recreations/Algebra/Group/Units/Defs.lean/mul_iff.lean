import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem mul_iff [Monoid M] [IsDedekindFiniteMonoid M] {x y : M} :
    IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y := ⟨fun h => ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩,
   fun h => IsUnit.mul h.1 h.2⟩

