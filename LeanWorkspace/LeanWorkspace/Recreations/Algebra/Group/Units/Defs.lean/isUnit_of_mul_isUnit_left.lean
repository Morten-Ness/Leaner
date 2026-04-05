import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem isUnit_of_mul_isUnit_left [Monoid M] [IsDedekindFiniteMonoid M] {x y : M}
    (hu : IsUnit (x * y)) : IsUnit x := let ⟨z, hz⟩ := isUnit_iff_exists_inv.1 hu
  isUnit_iff_exists_inv.2 ⟨y * z, by rwa [← mul_assoc]⟩

