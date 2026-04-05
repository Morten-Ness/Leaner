import Mathlib

variable {M : Type*}

theorem Associated.prime_iff [CommMonoidWithZero M] {p q : M} (h : p ~ᵤ q) : Prime p ↔ Prime q := ⟨h.prime, Associated.symm h.prime⟩

