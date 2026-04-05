import Mathlib

variable {G H M N α : Type*}

theorem smul_eq_mul {M} [CommMonoid M] (u₁ u₂ : Mˣ) :
    u₁ • u₂ = u₁ * u₂ := by
  fail_if_success rfl -- there is an instance diamond here
  ext
  rfl

