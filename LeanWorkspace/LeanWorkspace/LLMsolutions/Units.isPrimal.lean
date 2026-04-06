FAIL
import Mathlib

variable {α : Type*}

variable [Monoid α] {a b u : α}

theorem isPrimal (hu : IsUnit u) : IsPrimal u := by
  intro b c h
  refine ⟨u, 1, ?_, ?_, by simp⟩
  · exact dvd_rfl
  · simpa using h
