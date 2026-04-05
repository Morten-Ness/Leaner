import Mathlib

variable {R ι : Type*}

variable [CommRing R] [CharP R 2] [NoZeroDivisors R]

private def sqAddMonoidHom : R →+ R where
  toFun := (· ^ 2)
  map_zero' := zero_pow two_ne_zero
  map_add' := CharTwo.add_sq


theorem sq_injective : Function.Injective fun x : R ↦ x ^ 2 := by
  intro x y h
  rwa [← CharTwo.add_eq_zero, ← CharTwo.add_sq, pow_eq_zero_iff two_ne_zero, CharTwo.add_eq_zero] at h

