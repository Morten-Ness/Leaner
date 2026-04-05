import Mathlib

variable {ι : Type*}

theorem next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Rel i j) : c.next i = j := by
  apply c.next_eq _ h
  rw [ComplexShape.next]
  rw [dif_pos]
  exact Exists.choose_spec ⟨j, h⟩

