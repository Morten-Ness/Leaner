import Mathlib

variable {R A B : Type*}

theorem commute_eps_left [Semiring R] (x : DualNumber R) : Commute ε x := by
  ext <;> simp

