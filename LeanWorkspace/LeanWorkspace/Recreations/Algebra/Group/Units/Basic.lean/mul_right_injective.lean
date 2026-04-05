import Mathlib

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem mul_right_injective (h : IsUnit a) : Function.Injective (a * ·) := fun _ _ => IsUnit.mul_left_cancel h

