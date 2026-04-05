import Mathlib

variable {F α β : Type*}

variable {α : Type*} {f : α → α} {n : ℕ}

theorem iterate_two_mul_add_one (hf : Function.Involutive f) (n : ℕ) : f^[2 * n + 1] = f := by
  rw [iterate_succ, Function.Involutive.iterate_two_mul hf, id_comp]

