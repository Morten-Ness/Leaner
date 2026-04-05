import Mathlib

variable {M N : Type*}

theorem DvdNotUnit.isUnit_of_irreducible_right [CommMonoidWithZero M] {p q : M}
    (h : DvdNotUnit p q) (hq : Irreducible q) : IsUnit p := by
  obtain ⟨_, x, hx, hx'⟩ := h
  exact ((irreducible_iff.1 hq).right hx').resolve_right hx

