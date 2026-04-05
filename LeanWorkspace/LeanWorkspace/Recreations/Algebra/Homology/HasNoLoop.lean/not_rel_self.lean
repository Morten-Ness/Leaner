import Mathlib

variable {ι : Type*}

variable (c : ComplexShape ι) [c.HasNoLoop] (j : ι)

theorem not_rel_self : ¬ c.Rel j j := HasNoLoop.not_rel_self j

