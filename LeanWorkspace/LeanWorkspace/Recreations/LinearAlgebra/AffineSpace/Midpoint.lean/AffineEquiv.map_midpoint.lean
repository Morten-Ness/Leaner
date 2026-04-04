import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

theorem AffineEquiv.map_midpoint (f : P ≃ᵃ[R] P') (a b : P) :
    f (midpoint R a b) = midpoint R (f a) (f b) := f.apply_lineMap a b _

