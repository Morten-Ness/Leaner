import Mathlib

variable {F α β : Type*}

variable {α : Type*} {f : α → α} {n : ℕ}

theorem iterate_two_mul (hf : Function.Involutive f) (n : ℕ) : f^[2 * n] = id := by
  rw [iterate_mul, involutive_iff_iter_2_eq_id.1 hf, iterate_id]

