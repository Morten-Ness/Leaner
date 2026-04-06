FAIL
import Mathlib

variable {α : Type u}

variable {β : Type v} (f : α → β)

theorem length_map (x) : (FreeSemigroup.map f x).length = x.length := by
  rcases x with ⟨l, hne⟩
  rfl
