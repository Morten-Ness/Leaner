FAIL
import Mathlib

variable {ι : Type*}

theorem next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Rel i j) : c.next i = j := by
  simpa [ComplexShape.Rel] using h
