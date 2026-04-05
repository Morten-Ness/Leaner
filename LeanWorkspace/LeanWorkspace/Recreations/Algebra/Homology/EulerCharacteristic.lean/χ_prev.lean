import Mathlib

variable {ι : Type*} (c : ComplexShape ι)

variable [c.EulerCharSigns]

theorem χ_prev {i j : ι} (h : c.Rel i j) : c.χ i = - c.χ j := by simp [ComplexShape.χ_next c h]

