import Mathlib

variable {M : Type*}

theorem associated_mul_unit_left {N : Type*} [Monoid N] (a u : N) (hu : IsUnit u) :
    Associated (a * u) a := let ⟨u', hu⟩ := hu
  ⟨u'⁻¹, hu ▸ Units.mul_inv_cancel_right _ _⟩

