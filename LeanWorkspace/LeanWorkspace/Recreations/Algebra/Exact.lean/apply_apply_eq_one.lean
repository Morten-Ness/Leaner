import Mathlib

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem apply_apply_eq_one [One P] (h : Function.MulExact f g) (x : M) :
    g (f x) = 1 := (h _).mpr <| Set.mem_range_self _

