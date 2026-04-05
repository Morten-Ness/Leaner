import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem isUnit_of_mul_isUnit_right [Monoid M] [IsDedekindFiniteMonoid M] {x y : M}
    (hu : IsUnit (x * y)) : IsUnit y := let ⟨z, hz⟩ := isUnit_iff_exists_inv'.1 hu
  isUnit_iff_exists_inv'.2 ⟨z * x, by rwa [mul_assoc]⟩

