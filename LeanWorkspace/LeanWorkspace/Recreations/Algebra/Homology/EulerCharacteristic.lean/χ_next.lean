import Mathlib

variable {ι : Type*} (c : ComplexShape ι)

variable [c.EulerCharSigns]

theorem χ_next {i j : ι} (h : c.Rel i j) : c.χ j = - c.χ i := EulerCharSigns.χ_next h

