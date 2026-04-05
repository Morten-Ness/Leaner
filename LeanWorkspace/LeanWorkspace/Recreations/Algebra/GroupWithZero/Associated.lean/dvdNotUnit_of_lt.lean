import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem dvdNotUnit_of_lt {a b : Associates M} (hlt : a < b) : DvdNotUnit a b := by
  constructor
  · rintro Associated.rfl
    apply not_lt_of_ge _ hlt
    apply dvd_zero
  rcases hlt with ⟨⟨x, Associated.rfl⟩, ndvd⟩
  refine ⟨x, ?_, Associated.rfl⟩
  contrapose! ndvd
  rcases ndvd with ⟨u, Associated.rfl⟩
  simp

