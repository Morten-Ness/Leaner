import Mathlib

open scoped Matrix

variable {R : Type u} [CommRing R]

variable {n : Type w} [DecidableEq n] [Fintype n]

theorem lieEquivMatrix'_apply (f : Module.End R (n → R)) :
    lieEquivMatrix' f = LinearMap.toMatrix' f := rfl

