import Mathlib

variable {M N : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

theorem DvdNotUnit.ne {p q : M} (h : DvdNotUnit p q) : p ≠ q := by
  by_contra hcontra
  obtain ⟨hp, x, hx', hx''⟩ := h
  simp_all

