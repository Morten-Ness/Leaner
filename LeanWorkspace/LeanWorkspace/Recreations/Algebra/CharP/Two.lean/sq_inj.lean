import Mathlib

variable {R ι : Type*}

variable [CommRing R] [CharP R 2] [NoZeroDivisors R]

private def sqAddMonoidHom : R →+ R where
  toFun := (· ^ 2)
  map_zero' := zero_pow two_ne_zero
  map_add' := CharTwo.add_sq


theorem sq_inj {x y : R} : x ^ 2 = y ^ 2 ↔ x = y := CharTwo.sq_injective.eq_iff

