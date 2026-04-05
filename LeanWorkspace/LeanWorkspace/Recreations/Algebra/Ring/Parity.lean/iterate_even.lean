import Mathlib

variable {F α β : Type*}

variable {α : Type*} {f : α → α} {n : ℕ}

theorem iterate_even (hf : Function.Involutive f) (hn : Even n) : f^[n] = id := by
  obtain ⟨m, rfl⟩ := hn
  rw [← two_mul, Function.Involutive.iterate_two_mul hf]

