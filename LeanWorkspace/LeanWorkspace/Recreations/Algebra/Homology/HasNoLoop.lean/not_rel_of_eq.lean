import Mathlib

variable {ι : Type*}

variable (c : ComplexShape ι) [c.HasNoLoop] (j : ι)

theorem not_rel_of_eq {j' : ι} (h : j = j') : ¬ c.Rel j j' := by
  subst h
  exact ComplexShape.not_rel_self c j

