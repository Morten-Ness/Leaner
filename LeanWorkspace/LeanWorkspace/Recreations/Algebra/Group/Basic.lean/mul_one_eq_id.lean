import Mathlib

variable {α β G M : Type*}

variable [MulOneClass M]

theorem mul_one_eq_id : (· * (1 : M)) = id := funext mul_one

