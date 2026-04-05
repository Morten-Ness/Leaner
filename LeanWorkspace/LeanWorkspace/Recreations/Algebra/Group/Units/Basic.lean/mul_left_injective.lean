import Mathlib

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem mul_left_injective (h : IsUnit b) : Function.Injective (· * b) := fun _ _ => IsUnit.mul_right_cancel h

