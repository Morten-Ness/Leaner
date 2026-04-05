import Mathlib

variable {M : Type*}

theorem Irreducible.dvd_iff [Monoid M] {x y : M} (hx : Irreducible x) :
    y ∣ x ↔ IsUnit y ∨ Associated x y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain (h | h) := hx.isUnit_or_isUnit hz
    · exact Or.inl h
    · rw [hz]
      exact Or.inr (associated_mul_unit_left _ _ h)
  · rintro (hy | h)
    · exact hy.dvd
    · exact Associated.symm h.dvd

