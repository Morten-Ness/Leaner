import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem Irreducible.prime_of_isPrimal {a : M}
    (irr : Irreducible a) (primal : IsPrimal a) : Prime a := ⟨Prime.ne_zero irr, irr.not_isUnit, fun a b dvd ↦ by
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := primal dvd
    exact (of_irreducible_mul irr).symm.imp (·.mul_right_dvd.mpr h₁) (·.mul_left_dvd.mpr h₂)⟩

