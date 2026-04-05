import Mathlib

variable {F α β : Type*}

variable {α : Type*} {f : α → α} {n : ℕ}

theorem iterate_odd (hf : Function.Involutive f) (hn : Odd n) : f^[n] = f := by
  obtain ⟨m, rfl⟩ := hn
  rw [iterate_add, Function.Involutive.iterate_two_mul hf, id_comp, iterate_one]

