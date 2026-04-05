import Mathlib

variable {M : Type*}

theorem DvdNotUnit.not_associated [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M}
    (h : DvdNotUnit p q) : ¬Associated p q := by
  rintro ⟨a, Associated.rfl⟩
  obtain ⟨hp, x, hx, hx'⟩ := h
  rcases (mul_right_inj' hp).mp hx' with Associated.rfl
  exact hx a.isUnit

