import Mathlib

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem comp_eq_one [One P] (h : Function.MulExact f g) : g.comp f = 1 := funext Function.MulExact.apply_apply_eq_one h

